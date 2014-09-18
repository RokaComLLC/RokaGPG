/* keygen.c - generate a key pair
 * Copyright (C) 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006,
 *               2007, 2009 Free Software Foundation, Inc.
 *
 * This file is part of GnuPG.
 *
 * GnuPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * GnuPG is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include "util.h"

#include "main.h"

 
#include "packet.h"
#include "cipher.h"


#include "ttyio.h"

#include "options.h"

#include "keydb.h"
#include "trustdb.h"
#include "status.h"
#include "i18n.h"
//#include "cardglue.h"
#include "keyserver-internal.h"
#include "types.h"
#include "memory.h"

#define MAX_PREFS 30

enum para_name {
  pKEYTYPE,
  pKEYLENGTH,
  pKEYUSAGE,
  pSUBKEYTYPE,
  pSUBKEYLENGTH,
  pSUBKEYUSAGE,
  pAUTHKEYTYPE,
  pNAMEREAL,
  pNAMEEMAIL,
  pNAMECOMMENT,
  pPREFERENCES,
  pREVOKER,
  pUSERID,
  pCREATIONDATE,
  pKEYCREATIONDATE, /* Same in seconds since epoch.  */
  pEXPIREDATE,
  pKEYEXPIRE, /* in n seconds */
  pSUBKEYEXPIRE, /* in n seconds */
  pPASSPHRASE,
  pPASSPHRASE_DEK,
  pPASSPHRASE_S2K,
  pSERIALNO,
  pBACKUPENCDIR,
  pHANDLE,
  pKEYSERVER
};




struct para_data_s {
    struct para_data_s *next;
    int lnr;
    enum para_name key;
    union {
        DEK *dek;
        STRING2KEY *s2k;
        u32 expire;
        u32 creation;
        unsigned int usage;
        struct revocation_key revkey;
        char value[1];
    } u;
};

struct output_control_s {
    int lnr;
    int dryrun;
    int use_files;
    struct {
	char  *fname;
	char  *newfname;
	IOBUF stream;
	armor_filter_context_t afx;
    } pub;
    struct {
	char  *fname;
	char  *newfname;
	IOBUF stream;
	armor_filter_context_t afx;
    } sec;
};


struct opaque_data_usage_and_pk {
    unsigned int usage;
    PKT_public_key *pk;
};


static int prefs_initialized = 0;
static byte sym_prefs[MAX_PREFS];
static int nsym_prefs;
static byte hash_prefs[MAX_PREFS];
static int nhash_prefs;
static byte zip_prefs[MAX_PREFS];
static int nzip_prefs;
static int mdc_available,ks_modify;



static void do_generate_keypair (struct para_data_s *para,
				 struct output_control_s *outctrl,
				 int card);
static int  write_keyblock( IOBUF out, KBNODE node );










static void
print_status_key_created (int letter, PKT_public_key *pk, const char *handle)
{
  byte array[MAX_FINGERPRINT_LEN], *s;
  char *buf, *p;
  size_t i, n;

  if (!handle)
    handle = "";

  buf = xmalloc (MAX_FINGERPRINT_LEN*2+31 + strlen (handle) + 1);

  p = buf;
  if (letter || pk)
    {
      *p++ = letter;
      *p++ = ' ';
      fingerprint_from_pk (pk, array, &n);
      s = array;
      for (i=0; i < n ; i++, s++, p += 2)
        sprintf (p, "%02X", *s);
    }
  if (*handle)
    {
      *p++ = ' ';
      for (i=0; handle[i] && i < 100; i++)
        *p++ = isspace ((unsigned int)handle[i])? '_':handle[i];
    }
  *p = 0;
  write_status_text ((letter || pk)?STATUS_KEY_CREATED:STATUS_KEY_NOT_CREATED,
                     buf);
  xfree (buf);
}

static void
print_status_key_not_created (const char *handle)
{
  print_status_key_created (0, NULL, handle);
}



static void
write_uid( KBNODE root, const char *s )
{
    PACKET *pkt = xmalloc_clear(sizeof *pkt );
    size_t n = strlen(s);

    pkt->pkttype = PKT_USER_ID;
    pkt->pkt.user_id = xmalloc_clear( sizeof *pkt->pkt.user_id + n - 1 );
    pkt->pkt.user_id->len = n;
    pkt->pkt.user_id->ref = 1;
    strcpy(pkt->pkt.user_id->name, s);
    add_kbnode( root, new_kbnode( pkt ) );
}


static void
do_add_key_flags (PKT_signature *sig, unsigned int use)
{
    byte buf[1];

    buf[0] = 0;

    /* The spec says that all primary keys MUST be able to certify. */
    if(sig->sig_class!=0x18)
      buf[0] |= 0x01;

    if (use & PUBKEY_USAGE_SIG)
      buf[0] |= 0x02;
    if (use & PUBKEY_USAGE_ENC)
        buf[0] |= 0x04 | 0x08;
    if (use & PUBKEY_USAGE_AUTH)
        buf[0] |= 0x20;

    build_sig_subpkt (sig, SIGSUBPKT_KEY_FLAGS, buf, 1);
}


int
keygen_add_key_expire( PKT_signature *sig, void *opaque )
{
    PKT_public_key *pk = opaque;
    byte buf[8];
    u32  u;

    if( pk->expiredate ) {
        if(pk->expiredate > pk->timestamp)
	  u= pk->expiredate - pk->timestamp;
	else
	  u= 1;

	buf[0] = (u >> 24) & 0xff;
	buf[1] = (u >> 16) & 0xff;
	buf[2] = (u >>	8) & 0xff;
	buf[3] = u & 0xff;
	build_sig_subpkt( sig, SIGSUBPKT_KEY_EXPIRE, buf, 4 );
    }
    else
      {
	/* Make sure we don't leave a key expiration subpacket lying
	   around */
	delete_sig_subpkt (sig->hashed, SIGSUBPKT_KEY_EXPIRE);
      }

    return 0;
}



static int
keygen_add_key_flags_and_expire (PKT_signature *sig, void *opaque)
{
    struct opaque_data_usage_and_pk *oduap = opaque;

    do_add_key_flags (sig, oduap->usage);
    return keygen_add_key_expire (sig, oduap->pk);
}








static int
set_one_pref (int val, int type, const char *item, byte *buf, int *nbuf)
{
    int i;

    for (i=0; i < *nbuf; i++ )
      if (buf[i] == val)
	{
	  fprintf(stderr,"preference `%s' duplicated\n", item);
	  return -1;
        }

    if (*nbuf >= MAX_PREFS)
      {
	if(type==1)
	  fprintf(stderr,"too many cipher preferences\n");
	else if(type==2)
	  fprintf(stderr,"too many digest preferences\n");
	else if(type==3)
	  fprintf(stderr,"too many compression preferences\n");
	else
	  BUG();

        return -1;
      }

    buf[(*nbuf)++] = val;
    return 0;
}



/*
 * Parse the supplied string and use it to set the standard
 * preferences.  The string may be in a form like the one printed by
 * "pref" (something like: "S10 S3 H3 H2 Z2 Z1") or the actual
 * cipher/hash/compress names.  Use NULL to set the default
 * preferences.  Returns: 0 = okay
 */
int
keygen_set_std_prefs (const char *string,int personal)
{
    byte sym[MAX_PREFS], hash[MAX_PREFS], zip[MAX_PREFS];
    int nsym=0, nhash=0, nzip=0, val, rc=0;
    int mdc=1, modify=0; /* mdc defaults on, modify defaults off. */
    char dummy_string[20*4+1]; /* Enough for 20 items. */

    if (!string || !ascii_strcasecmp (string, "default"))
      {
	if (opt.def_preference_list)
	  string=opt.def_preference_list;
	else
	  {
	    dummy_string[0]='\0';

            /* The rationale why we use the order AES256,192,128 is
               for compatibility reasons with PGP.  If gpg would
               define AES128 first, we would get the somewhat
               confusing situation:

                 gpg -r pgpkey -r gpgkey  ---gives--> AES256
                 gpg -r gpgkey -r pgpkey  ---gives--> AES

               Note that by using --personal-cipher-preferences it is
               possible to prefer AES128.
            */

	    /* Make sure we do not add more than 15 items here, as we
	       could overflow the size of dummy_string.  We currently
	       have at most 12. */
	    if(!check_cipher_algo(CIPHER_ALGO_AES256))
	      strcat(dummy_string,"S9 ");
	    if(!check_cipher_algo(CIPHER_ALGO_AES192))
	      strcat(dummy_string,"S8 ");
	    if(!check_cipher_algo(CIPHER_ALGO_AES))
	      strcat(dummy_string,"S7 ");
	    if(!check_cipher_algo(CIPHER_ALGO_CAST5))
	      strcat(dummy_string,"S3 ");
	    strcat(dummy_string,"S2 "); /* 3DES */
	    /* If we have it and we are in PGP2 mode,
               IDEA goes *after* 3DES so it won't be
	       used unless we're encrypting along with a V3 key.
	       Ideally, we would only put the S1 preference in if the
	       key was RSA and <=2048 bits, as that is what won't
	       break PGP2, but that is difficult with the current
	       code, and not really worth checking as a non-RSA <=2048
	       bit key wouldn't be usable by PGP2 anyway. -dms */
	    if(PGP2 && !check_cipher_algo(CIPHER_ALGO_IDEA))
	      strcat(dummy_string,"S1 ");


            /* The default hash algo order is:
                 SHA-256, SHA-1, SHA-384, SHA-512, SHA-224.
               Ordering SHA-1 before SHA-384 might be viewed as a bit
               strange; it is done because we expect that soon enough
               SHA-3 will be available and at that point there should
               be no more need for SHA-384 etc.  Anyway this order is
               just a default and can easily be changed by a config
               option.  */
	    if (!check_digest_algo (DIGEST_ALGO_SHA256))
	      strcat (dummy_string, "H8 ");

	    strcat (dummy_string,"H2 ");/* SHA-1 */

	    if (!check_digest_algo (DIGEST_ALGO_SHA384))
	      strcat (dummy_string, "H9 ");

	    if (!check_digest_algo (DIGEST_ALGO_SHA512))
	      strcat (dummy_string, "H10 ");

	    if (!check_digest_algo (DIGEST_ALGO_SHA224))
	      strcat (dummy_string, "H11 ");


	    /* ZLIB */
	    strcat(dummy_string,"Z2 ");

	    if(!check_compress_algo(COMPRESS_ALGO_BZIP2))
	      strcat(dummy_string,"Z3 ");

	    /* ZIP */
	    strcat(dummy_string,"Z1");

	    string=dummy_string;
	  }
      }
    else if (!ascii_strcasecmp (string, "none"))
        string = "";

    if(strlen(string))
      {
	char *tok,*prefstring;

	prefstring=xstrdup(string); /* need a writable string! */

	while((tok=strsep(&prefstring," ,")))
	  {
	    if((val=string_to_cipher_algo(tok)))
	      {
		if(set_one_pref(val,1,tok,sym,&nsym))
		  rc=-1;
	      }
	    else if((val=string_to_digest_algo(tok)))
	      {
		if(set_one_pref(val,2,tok,hash,&nhash))
		  rc=-1;
	      }
	    else if((val=string_to_compress_algo(tok))>-1)
	      {
		if(set_one_pref(val,3,tok,zip,&nzip))
		  rc=-1;
	      }
	    else if (ascii_strcasecmp(tok,"mdc")==0)
	      mdc=1;
	    else if (ascii_strcasecmp(tok,"no-mdc")==0)
	      mdc=0;
	    else if (ascii_strcasecmp(tok,"ks-modify")==0)
	      modify=1;
	    else if (ascii_strcasecmp(tok,"no-ks-modify")==0)
	      modify=0;
	    else
	      {
		   fprintf(stderr, "invalid item `%s' in preference string\n",tok);
		rc=-1;
	      }
	  }

	xfree(prefstring);
      }

    if(!rc)
      {
	if(personal)
	  {
	    if(personal==PREFTYPE_SYM)
	      {
		xfree(opt.personal_cipher_prefs);

		if(nsym==0)
		  opt.personal_cipher_prefs=NULL;
		else
		  {
		    int i;

		    opt.personal_cipher_prefs=
		      xmalloc(sizeof(prefitem_t *)*(nsym+1));

		    for (i=0; i<nsym; i++)
		      {
			opt.personal_cipher_prefs[i].type = PREFTYPE_SYM;
			opt.personal_cipher_prefs[i].value = sym[i];
		      }

		    opt.personal_cipher_prefs[i].type = PREFTYPE_NONE;
		    opt.personal_cipher_prefs[i].value = 0;
		  }
	      }
	    else if(personal==PREFTYPE_HASH)
	      {
		xfree(opt.personal_digest_prefs);

		if(nhash==0)
		  opt.personal_digest_prefs=NULL;
		else
		  {
		    int i;

		    opt.personal_digest_prefs=
		      xmalloc(sizeof(prefitem_t *)*(nhash+1));

		    for (i=0; i<nhash; i++)
		      {
			opt.personal_digest_prefs[i].type = PREFTYPE_HASH;
			opt.personal_digest_prefs[i].value = hash[i];
		      }

		    opt.personal_digest_prefs[i].type = PREFTYPE_NONE;
		    opt.personal_digest_prefs[i].value = 0;
		  }
	      }
	    else if(personal==PREFTYPE_ZIP)
	      {
		xfree(opt.personal_compress_prefs);

		if(nzip==0)
		  opt.personal_compress_prefs=NULL;
		else
		  {
		    int i;

		    opt.personal_compress_prefs=
		      xmalloc(sizeof(prefitem_t *)*(nzip+1));

		    for (i=0; i<nzip; i++)
		      {
			opt.personal_compress_prefs[i].type = PREFTYPE_ZIP;
			opt.personal_compress_prefs[i].value = zip[i];
		      }

		    opt.personal_compress_prefs[i].type = PREFTYPE_NONE;
		    opt.personal_compress_prefs[i].value = 0;
		  }
	      }
	  }
	else
	  {
	    memcpy (sym_prefs,  sym,  (nsym_prefs=nsym));
	    memcpy (hash_prefs, hash, (nhash_prefs=nhash));
	    memcpy (zip_prefs,  zip,  (nzip_prefs=nzip));
	    mdc_available = mdc;
	    ks_modify = modify;
	    prefs_initialized = 1;
	  }
      }

    return rc;
}

#ifdef ERNIE

/* Return a fake user ID containing the preferences.  Caller must
   free. */
PKT_user_id *
keygen_get_std_prefs (void)
{
  int i,j=0;
  PKT_user_id *uid=xmalloc_clear(sizeof(PKT_user_id));

  if(!prefs_initialized)
    keygen_set_std_prefs(NULL,0);

  uid->ref=1;

  uid->prefs=xmalloc((sizeof(prefitem_t *)*
		      (nsym_prefs+nhash_prefs+nzip_prefs+1)));

  for(i=0;i<nsym_prefs;i++,j++)
    {
      uid->prefs[j].type=PREFTYPE_SYM;
      uid->prefs[j].value=sym_prefs[i];
    }

  for(i=0;i<nhash_prefs;i++,j++)
    {
      uid->prefs[j].type=PREFTYPE_HASH;
      uid->prefs[j].value=hash_prefs[i];
    }

  for(i=0;i<nzip_prefs;i++,j++)
    {
      uid->prefs[j].type=PREFTYPE_ZIP;
      uid->prefs[j].value=zip_prefs[i];
    }

  uid->prefs[j].type=PREFTYPE_NONE;
  uid->prefs[j].value=0;

  uid->flags.mdc=mdc_available;
  uid->flags.ks_modify=ks_modify;

  return uid;
}
#endif


static void
add_feature_mdc (PKT_signature *sig,int enabled)
{
    const byte *s;
    size_t n;
    int i;
    char *buf;

    s = parse_sig_subpkt (sig->hashed, SIGSUBPKT_FEATURES, &n );
    /* Already set or cleared */
    if (s && n &&
	((enabled && (s[0] & 0x01)) || (!enabled && !(s[0] & 0x01))))
      return;

    if (!s || !n) { /* create a new one */
        n = 1;
        buf = xmalloc_clear (n);
    }
    else {
        buf = xmalloc (n);
        memcpy (buf, s, n);
    }

    if(enabled)
      buf[0] |= 0x01; /* MDC feature */
    else
      buf[0] &= ~0x01;

    /* Are there any bits set? */
    for(i=0;i<n;i++)
      if(buf[i]!=0)
	break;

    if(i==n)
      delete_sig_subpkt (sig->hashed, SIGSUBPKT_FEATURES);
    else
      build_sig_subpkt (sig, SIGSUBPKT_FEATURES, buf, n);

    xfree (buf);
}

static void
add_keyserver_modify (PKT_signature *sig,int enabled)
{
  const byte *s;
  size_t n;
  int i;
  char *buf;

  /* The keyserver modify flag is a negative flag (i.e. no-modify) */
  enabled=!enabled;

  s = parse_sig_subpkt (sig->hashed, SIGSUBPKT_KS_FLAGS, &n );
  /* Already set or cleared */
  if (s && n &&
      ((enabled && (s[0] & 0x80)) || (!enabled && !(s[0] & 0x80))))
    return;

  if (!s || !n) { /* create a new one */
    n = 1;
    buf = xmalloc_clear (n);
  }
  else {
    buf = xmalloc (n);
    memcpy (buf, s, n);
  }

  if(enabled)
    buf[0] |= 0x80; /* no-modify flag */
  else
    buf[0] &= ~0x80;

  /* Are there any bits set? */
  for(i=0;i<n;i++)
    if(buf[i]!=0)
      break;

  if(i==n)
    delete_sig_subpkt (sig->hashed, SIGSUBPKT_KS_FLAGS);
  else
    build_sig_subpkt (sig, SIGSUBPKT_KS_FLAGS, buf, n);

  xfree (buf);
}


int
keygen_upd_std_prefs( PKT_signature *sig, void *opaque )
{
    (void)opaque;

    if (!prefs_initialized)
        keygen_set_std_prefs (NULL, 0);

    if (nsym_prefs)
        build_sig_subpkt (sig, SIGSUBPKT_PREF_SYM, sym_prefs, nsym_prefs);
    else
      {
        delete_sig_subpkt (sig->hashed, SIGSUBPKT_PREF_SYM);
        delete_sig_subpkt (sig->unhashed, SIGSUBPKT_PREF_SYM);
      }

    if (nhash_prefs)
        build_sig_subpkt (sig, SIGSUBPKT_PREF_HASH, hash_prefs, nhash_prefs);
    else
      {
	delete_sig_subpkt (sig->hashed, SIGSUBPKT_PREF_HASH);
	delete_sig_subpkt (sig->unhashed, SIGSUBPKT_PREF_HASH);
      }

    if (nzip_prefs)
        build_sig_subpkt (sig, SIGSUBPKT_PREF_COMPR, zip_prefs, nzip_prefs);
    else
      {
        delete_sig_subpkt (sig->hashed, SIGSUBPKT_PREF_COMPR);
        delete_sig_subpkt (sig->unhashed, SIGSUBPKT_PREF_COMPR);
      }

    /* Make sure that the MDC feature flag is set if needed */
    add_feature_mdc (sig,mdc_available);
    add_keyserver_modify (sig,ks_modify);
    keygen_add_keyserver_url(sig,NULL);

    return 0;
}



/****************
 * Add preference to the self signature packet.
 * This is only called for packets with version > 3.

 */
int
keygen_add_std_prefs( PKT_signature *sig, void *opaque )
{
    PKT_public_key *pk = opaque;

    do_add_key_flags (sig, pk->pubkey_usage);
    keygen_add_key_expire( sig, opaque );
    keygen_upd_std_prefs (sig, opaque);
    keygen_add_keyserver_url(sig,NULL);

    return 0;
}



int
keygen_add_keyserver_url(PKT_signature *sig, void *opaque)
{
  const char *url=opaque;

  if(!url)
    url=opt.def_keyserver_url;

  if(url)
    build_sig_subpkt(sig,SIGSUBPKT_PREF_KS,url,strlen(url));
  else
    delete_sig_subpkt (sig->hashed,SIGSUBPKT_PREF_KS);

  return 0;
}


int
keygen_add_notations(PKT_signature *sig,void *opaque)
{
  struct notation *notation;

  /* We always start clean */
  delete_sig_subpkt(sig->hashed,SIGSUBPKT_NOTATION);
  delete_sig_subpkt(sig->unhashed,SIGSUBPKT_NOTATION);
  sig->flags.notation=0;

  for(notation=opaque;notation;notation=notation->next)
    if(!notation->flags.ignore)
      {
	unsigned char *buf;
	unsigned int n1,n2;

	n1=strlen(notation->name);
	if(notation->altvalue)
	  n2=strlen(notation->altvalue);
	else if(notation->bdat)
	  n2=notation->blen;
	else
	  n2=strlen(notation->value);

	buf = xmalloc( 8 + n1 + n2 );

	/* human readable or not */
	buf[0] = notation->bdat?0:0x80;
	buf[1] = buf[2] = buf[3] = 0;
	buf[4] = n1 >> 8;
	buf[5] = n1;
	buf[6] = n2 >> 8;
	buf[7] = n2;
	memcpy(buf+8, notation->name, n1 );
	if(notation->altvalue)
	  memcpy(buf+8+n1, notation->altvalue, n2 );
	else if(notation->bdat)
	  memcpy(buf+8+n1, notation->bdat, n2 );
	else
	  memcpy(buf+8+n1, notation->value, n2 );
	build_sig_subpkt( sig, SIGSUBPKT_NOTATION |
			  (notation->flags.critical?SIGSUBPKT_FLAG_CRITICAL:0),
			  buf, 8+n1+n2 );
	xfree(buf);
      }

  return 0;
}



int
keygen_add_revkey(PKT_signature *sig, void *opaque)
{
  struct revocation_key *revkey=opaque;
  byte buf[2+MAX_FINGERPRINT_LEN];

  buf[0]=revkey->class;
  buf[1]=revkey->algid;
  memcpy(&buf[2],revkey->fpr,MAX_FINGERPRINT_LEN);

  build_sig_subpkt(sig,SIGSUBPKT_REV_KEY,buf,2+MAX_FINGERPRINT_LEN);

  /* All sigs with revocation keys set are nonrevocable */
  sig->flags.revocable=0;
  buf[0] = 0;
  build_sig_subpkt( sig, SIGSUBPKT_REVOCABLE, buf, 1 );

  parse_revkeys(sig);

  return 0;
}



/* Create a back-signature.  If TIMESTAMP is not NULL, use it for the
   signature creation time.  */
int
make_backsig (PKT_signature *sig, PKT_public_key *pk,
 	      PKT_public_key *sub_pk, PKT_secret_key *sub_sk,
              u32 timestamp)
{
  PKT_signature *backsig;
  int rc;

  cache_public_key(sub_pk);

  rc= make_keysig_packet (&backsig, pk, NULL, sub_pk, sub_sk, 0x19,
                          0, 0, timestamp, 0, NULL, NULL);
  if(rc)
    log_error("make_keysig_packet failed for backsig: %s\n",g10_errstr(rc));
  else
    {
      /* get it into a binary packed form. */
      IOBUF backsig_out=iobuf_temp();
      PACKET backsig_pkt;

      init_packet(&backsig_pkt);
      backsig_pkt.pkttype=PKT_SIGNATURE;
      backsig_pkt.pkt.signature=backsig;
      rc=build_packet(backsig_out,&backsig_pkt);
      free_packet(&backsig_pkt);
      if(rc)
	log_error("build_packet failed for backsig: %s\n",g10_errstr(rc));
      else
	{
	  size_t pktlen=0;
	  byte *buf=iobuf_get_temp_buffer(backsig_out);

	  /* Remove the packet header */
	  if(buf[0]&0x40)
	    {
	      if(buf[1]<192)
		{
		  pktlen=buf[1];
		  buf+=2;
		}
	      else if(buf[1]<224)
		{
		  pktlen=(buf[1]-192)*256;
		  pktlen+=buf[2]+192;
		  buf+=3;
		}
	      else if(buf[1]==255)
		{
		  pktlen =buf[2] << 24;
		  pktlen|=buf[3] << 16;
		  pktlen|=buf[4] << 8;
		  pktlen|=buf[5];
		  buf+=6;
		}
	      else
		BUG();
	    }
	  else
	    {
	      int mark=1;

	      switch(buf[0]&3)
		{
		case 3:
		  BUG();
		  break;

		case 2:
		  pktlen =buf[mark++] << 24;
		  pktlen|=buf[mark++] << 16;

		case 1:
		  pktlen|=buf[mark++] << 8;

		case 0:
		  pktlen|=buf[mark++];
		}

	      buf+=mark;
	    }

	  /* now make the binary blob into a subpacket */
	  build_sig_subpkt(sig,SIGSUBPKT_SIGNATURE,buf,pktlen);

	  iobuf_close(backsig_out);
	}
    }

  return rc;
}


static int
write_direct_sig( KBNODE root, KBNODE pub_root, PKT_secret_key *sk,
		  struct revocation_key *revkey, u32 timestamp)
{
    PACKET *pkt;
    PKT_signature *sig;
    int rc=0;
    KBNODE node;
    PKT_public_key *pk;

    if( opt.verbose )
	fprintf(stderr,"writing direct signature\n");

    /* get the pk packet from the pub_tree */
    node = find_kbnode( pub_root, PKT_PUBLIC_KEY );
    if( !node )
	BUG();
    pk = node->pkt->pkt.public_key;

    /* we have to cache the key, so that the verification of the signature
     * creation is able to retrieve the public key */
    cache_public_key (pk);

    /* and make the signature */
    rc = make_keysig_packet (&sig, pk, NULL, NULL, sk, 0x1F,
                             0, 0, timestamp, 0,
                             keygen_add_revkey, revkey);
    if( rc ) {
        log_error("make_keysig_packet failed: %s\n", g10_errstr(rc) );
        return rc;
    }

    pkt = xmalloc_clear( sizeof *pkt );
    pkt->pkttype = PKT_SIGNATURE;
    pkt->pkt.signature = sig;
    add_kbnode( root, new_kbnode( pkt ) );
    return rc;
}



static int
write_selfsigs (KBNODE sec_root, KBNODE pub_root, PKT_secret_key *sk,
		unsigned int use, u32 timestamp)
{
    PACKET *pkt;
    PKT_signature *sig;
    PKT_user_id *uid;
    int rc=0;
    KBNODE node;
    PKT_public_key *pk;

    if( opt.verbose ){
	  fprintf(stderr,"writing self signature\n");
    }

    /* get the uid packet from the list */
    node = find_kbnode( pub_root, PKT_USER_ID );
    if( !node )
	BUG(); /* no user id packet in tree */
    uid = node->pkt->pkt.user_id;
    /* get the pk packet from the pub_tree */
    node = find_kbnode( pub_root, PKT_PUBLIC_KEY );
    if( !node )
	BUG();
    pk = node->pkt->pkt.public_key;
    pk->pubkey_usage = use;
    /* we have to cache the key, so that the verification of the signature
     * creation is able to retrieve the public key */
    cache_public_key (pk);

    /* and make the signature */
    rc = make_keysig_packet (&sig, pk, uid, NULL, sk, 0x13,
                             0, 0, timestamp, 0,
                             keygen_add_std_prefs, pk);
    if( rc ) {
	log_error("make_keysig_packet failed: %s\n", g10_errstr(rc) );
	return rc;
    }

    pkt = xmalloc_clear( sizeof *pkt );
    pkt->pkttype = PKT_SIGNATURE;
    pkt->pkt.signature = sig;
    add_kbnode( sec_root, new_kbnode( pkt ) );

    pkt = xmalloc_clear( sizeof *pkt );
    pkt->pkttype = PKT_SIGNATURE;
    pkt->pkt.signature = copy_signature(NULL,sig);
    add_kbnode( pub_root, new_kbnode( pkt ) );
    return rc;
}



static int
write_keybinding (KBNODE root, KBNODE pub_root,
		  PKT_secret_key *pri_sk, PKT_secret_key *sub_sk,
                  unsigned int use, u32 timestamp)
{
    PACKET *pkt;
    PKT_signature *sig;
    int rc=0;
    KBNODE node;
    PKT_public_key *pri_pk, *sub_pk;
    struct opaque_data_usage_and_pk oduap;

    if( opt.verbose ){
	   fprintf(stderr,"writing key binding signature\n");
    }

    /* get the pk packet from the pub_tree */
    node = find_kbnode( pub_root, PKT_PUBLIC_KEY );
    if( !node )
	BUG();
    pri_pk = node->pkt->pkt.public_key;
    /* we have to cache the key, so that the verification of the signature
     * creation is able to retrieve the public key */
    cache_public_key (pri_pk);

    /* find the last subkey */
    sub_pk = NULL;
    for(node=pub_root; node; node = node->next ) {
	if( node->pkt->pkttype == PKT_PUBLIC_SUBKEY )
	    sub_pk = node->pkt->pkt.public_key;
    }
    if( !sub_pk )
	BUG();

    /* and make the signature */
    oduap.usage = use;
    oduap.pk = sub_pk;
    rc=make_keysig_packet(&sig, pri_pk, NULL, sub_pk, pri_sk, 0x18,
                          0, 0, timestamp, 0,
			  keygen_add_key_flags_and_expire, &oduap );
    if( rc ) {
	log_error("make_keysig_packet failed: %s\n", g10_errstr(rc) );
	return rc;
    }

    /* make a backsig */
    if(use&PUBKEY_USAGE_SIG)
      {
	rc = make_backsig (sig, pri_pk, sub_pk, sub_sk, timestamp);
	if(rc)
	  return rc;
      }

    pkt = xmalloc_clear( sizeof *pkt );
    pkt->pkttype = PKT_SIGNATURE;
    pkt->pkt.signature = sig;
    add_kbnode( root, new_kbnode( pkt ) );
    return rc;
}



static int
gen_elg(int algo, unsigned nbits, KBNODE pub_root, KBNODE sec_root, DEK *dek,
	STRING2KEY *s2k, PKT_secret_key **ret_sk, u32 timestamp,
	u32 expireval, int is_subkey)
{
    int rc;
    PACKET *pkt;
    PKT_secret_key *sk;
    PKT_public_key *pk;
    MPI skey[4];
    MPI *factors;

    assert( is_ELGAMAL(algo) );

    if (nbits < 1024) {
	nbits = 2048;
	 fprintf(stderr,"keysize invalid; using %u bits\n", nbits );
    }
    else if (nbits > 4096) {
        nbits = 4096;
        fprintf(stderr,"keysize invalid; using %u bits\n", nbits );
    }

    if( (nbits % 32) ) {
        nbits = ((nbits + 31) / 32) * 32;
        fprintf(stderr,"keysize rounded up to %u bits\n", nbits );
    }

    rc = pubkey_generate( algo, nbits, skey, &factors );
    if( rc ) {
	log_error("pubkey_generate failed: %s\n", g10_errstr(rc) );
	return rc;
    }

    sk = xmalloc_clear( sizeof *sk );
    pk = xmalloc_clear( sizeof *pk );
    sk->timestamp = pk->timestamp = timestamp;
    sk->version = pk->version = 4;
    if( expireval )
      sk->expiredate = pk->expiredate = sk->timestamp + expireval;

    sk->pubkey_algo = pk->pubkey_algo = algo;
		       pk->pkey[0] = mpi_copy_gpg( skey[0] );
		       pk->pkey[1] = mpi_copy_gpg( skey[1] );
		       pk->pkey[2] = mpi_copy_gpg( skey[2] );
    sk->skey[0] = skey[0];
    sk->skey[1] = skey[1];
    sk->skey[2] = skey[2];
    sk->skey[3] = skey[3];
    sk->is_protected = 0;
    sk->protect.algo = 0;

    sk->csum = checksum_mpi( sk->skey[3] );
    if( ret_sk ) /* return an unprotected version of the sk */
	*ret_sk = copy_secret_key( NULL, sk );

    if( dek ) {
	sk->protect.algo = dek->algo;
	sk->protect.s2k = *s2k;
	rc = protect_secret_key( sk, dek );
	if( rc ) {
	    log_error("protect_secret_key failed: %s\n", g10_errstr(rc) );
	    free_public_key(pk);
	    free_secret_key(sk);
	    return rc;
	}
    }

    pkt = xmalloc_clear(sizeof *pkt);
    pkt->pkttype = is_subkey ? PKT_PUBLIC_SUBKEY : PKT_PUBLIC_KEY;
    pkt->pkt.public_key = pk;
    add_kbnode(pub_root, new_kbnode( pkt ));

    /* don't know whether it makes sense to have the factors, so for now
     * we store them in the secret keyring (but they are not secret) */
    pkt = xmalloc_clear(sizeof *pkt);
    pkt->pkttype = is_subkey ? PKT_SECRET_SUBKEY : PKT_SECRET_KEY;
    pkt->pkt.secret_key = sk;
    add_kbnode(sec_root, new_kbnode( pkt ));

    return 0;
}


/****************
 * Generate a DSA key
 */
static int
gen_dsa(unsigned int nbits, KBNODE pub_root, KBNODE sec_root, DEK *dek,
	STRING2KEY *s2k, PKT_secret_key **ret_sk, u32 timestamp,
	u32 expireval, int is_subkey)
{
    int rc;
    PACKET *pkt;
    PKT_secret_key *sk;
    PKT_public_key *pk;
    MPI skey[5];
    MPI *factors;
    unsigned int qbits;

    if( nbits < 768)
      {
          nbits = 2048;
          fprintf(stderr,"keysize invalid; using %u bits\n", nbits );
      }
    else if(nbits>3072)
      {
          nbits = 3072;
          fprintf(stderr,"keysize invalid; using %u bits\n", nbits );
      }

    if(nbits % 64)
      {
          nbits = ((nbits + 63) / 64) * 64;
          fprintf(stderr,"keysize rounded up to %u bits\n", nbits );
      }

    /* To comply with FIPS rules we round up to the next value unless
       in expert mode.  */
    if (!opt.expert && nbits > 1024 && (nbits % 1024))
      {
        nbits = ((nbits + 1023) / 1024) * 1024;
        fprintf(stderr,"keysize rounded up to %u bits\n", nbits );
      }

    /*
      Figure out a q size based on the key size.  FIPS 180-3 says:

      L = 1024, N = 160
      L = 2048, N = 224
      L = 2048, N = 256
      L = 3072, N = 256

      2048/256 is an odd pair since there is also a 2048/224 and
      3072/256.  Matching sizes is not a very exact science.

      We'll do 256 qbits for nbits over 2047, 224 for nbits over 1024
      but less than 2048, and 160 for 1024 (DSA1).
    */

    if(nbits>2047)
      qbits=256;
    else if(nbits>1024)
      qbits=224;
    else
      qbits=160;

    if(qbits!=160)
      log_info("WARNING: some OpenPGP programs can't"
	       " handle a DSA key with this digest size\n");

    rc = dsa2_generate( PUBKEY_ALGO_DSA, nbits, qbits, skey, &factors );
    if( rc )
      {
	log_error("dsa2_generate failed: %s\n", g10_errstr(rc) );
	return rc;
      }

    sk = xmalloc_clear( sizeof *sk );
    pk = xmalloc_clear( sizeof *pk );
    sk->timestamp = pk->timestamp = timestamp;
    sk->version = pk->version = 4;
    if( expireval )
      sk->expiredate = pk->expiredate = sk->timestamp + expireval;

    sk->pubkey_algo = pk->pubkey_algo = PUBKEY_ALGO_DSA;
		       pk->pkey[0] = mpi_copy_gpg( skey[0] );
		       pk->pkey[1] = mpi_copy_gpg( skey[1] );
		       pk->pkey[2] = mpi_copy_gpg( skey[2] );
		       pk->pkey[3] = mpi_copy_gpg( skey[3] );
    sk->skey[0] = skey[0];
    sk->skey[1] = skey[1];
    sk->skey[2] = skey[2];
    sk->skey[3] = skey[3];
    sk->skey[4] = skey[4];
    sk->is_protected = 0;
    sk->protect.algo = 0;

    sk->csum = checksum_mpi ( sk->skey[4] );
    if( ret_sk ) /* return an unprotected version of the sk */
	*ret_sk = copy_secret_key( NULL, sk );

    if( dek ) {
	sk->protect.algo = dek->algo;
	sk->protect.s2k = *s2k;
	rc = protect_secret_key( sk, dek );
	if( rc ) {
	    log_error("protect_secret_key failed: %s\n", g10_errstr(rc) );
	    free_public_key(pk);
	    free_secret_key(sk);
	    return rc;
	}
    }

    pkt = xmalloc_clear(sizeof *pkt);
    pkt->pkttype = is_subkey ? PKT_PUBLIC_SUBKEY : PKT_PUBLIC_KEY;
    pkt->pkt.public_key = pk;
    add_kbnode(pub_root, new_kbnode( pkt ));

    /* don't know whether it makes sense to have the factors, so for now
     * we store them in the secret keyring (but they are not secret)
     * p = 2 * q * f1 * f2 * ... * fn
     * We store only f1 to f_n-1;  fn can be calculated because p and q
     * are known.
     */
    pkt = xmalloc_clear(sizeof *pkt);
    pkt->pkttype = is_subkey ? PKT_SECRET_SUBKEY : PKT_SECRET_KEY;
    pkt->pkt.secret_key = sk;
    add_kbnode(sec_root, new_kbnode( pkt ));

    return 0;
}


/*
 * Generate an RSA key.
 */
static int
gen_rsa(int algo, unsigned nbits, KBNODE pub_root, KBNODE sec_root, DEK *dek,
	STRING2KEY *s2k, PKT_secret_key **ret_sk, u32 timestamp,
	u32 expireval, int is_subkey)
{
    int rc;
    PACKET *pkt;
    PKT_secret_key *sk;
    PKT_public_key *pk;
    MPI skey[6];
    MPI *factors;

    assert( is_RSA(algo) );

    if( nbits < 1024 ) {
	   nbits = 2048;
	   fprintf(stderr,"keysize invalid; using %u bits\n", nbits );
    }
    else if (nbits > 4096) {
        nbits = 4096;
        fprintf(stderr,"keysize invalid; using %u bits\n", nbits );
    }

    if( (nbits % 32) ) {
        nbits = ((nbits + 31) / 32) * 32;
        fprintf(stderr,"keysize rounded up to %u bits\n", nbits );
    }

    rc = pubkey_generate( algo, nbits, skey, &factors );
    if( rc ) {
        log_error("pubkey_generate failed: %s\n", g10_errstr(rc) );
        return rc;
    }

    sk = xmalloc_clear( sizeof *sk );
    pk = xmalloc_clear( sizeof *pk );
    sk->timestamp = pk->timestamp = timestamp;
    sk->version = pk->version = 4;
    if( expireval )
      sk->expiredate = pk->expiredate = sk->timestamp + expireval;

    sk->pubkey_algo = pk->pubkey_algo = algo;
		       pk->pkey[0] = mpi_copy_gpg( skey[0] );
		       pk->pkey[1] = mpi_copy_gpg( skey[1] );
    sk->skey[0] = skey[0];
    sk->skey[1] = skey[1];
    sk->skey[2] = skey[2];
    sk->skey[3] = skey[3];
    sk->skey[4] = skey[4];
    sk->skey[5] = skey[5];
    sk->is_protected = 0;
    sk->protect.algo = 0;

    sk->csum  = checksum_mpi (sk->skey[2] );
    sk->csum += checksum_mpi (sk->skey[3] );
    sk->csum += checksum_mpi (sk->skey[4] );
    sk->csum += checksum_mpi (sk->skey[5] );
    if( ret_sk ) /* return an unprotected version of the sk */
	*ret_sk = copy_secret_key( NULL, sk );

    if( dek ) {
	sk->protect.algo = dek->algo;
	sk->protect.s2k = *s2k;
	rc = protect_secret_key( sk, dek );
	if( rc ) {
	    log_error("protect_secret_key failed: %s\n", g10_errstr(rc) );
	    free_public_key(pk);
	    free_secret_key(sk);
	    return rc;
	}
    }

    pkt = xmalloc_clear(sizeof *pkt);
    pkt->pkttype = is_subkey ? PKT_PUBLIC_SUBKEY : PKT_PUBLIC_KEY;
    pkt->pkt.public_key = pk;
    add_kbnode(pub_root, new_kbnode( pkt ));

    pkt = xmalloc_clear(sizeof *pkt);
    pkt->pkttype = is_subkey ? PKT_SECRET_SUBKEY : PKT_SECRET_KEY;
    pkt->pkt.secret_key = sk;
    add_kbnode(sec_root, new_kbnode( pkt ));

    return 0;
}



/****************
 * check valid days:
 * return 0 on error or the multiplier
 */
static int
check_valid_days( const char *s )
{
    if( !digitp(s) )
	return 0;
    for( s++; *s; s++)
	if( !digitp(s) )
	    break;
    if( !*s )
	return 1;
    if( s[1] )
	return 0; /* e.g. "2323wc" */
    if( *s == 'd' || *s == 'D' )
	return 1;
    if( *s == 'w' || *s == 'W' )
	return 7;
    if( *s == 'm' || *s == 'M' )
	return 30;
    if( *s == 'y' || *s == 'Y' )
	return 365;
    return 0;
}

#ifdef ERNIE

static void
print_key_flags(int flags)
{
  if(flags&PUBKEY_USAGE_SIG)
    tty_printf("%s ",_("Sign"));

  if(flags&PUBKEY_USAGE_CERT)
    tty_printf("%s ",_("Certify"));

  if(flags&PUBKEY_USAGE_ENC)
    tty_printf("%s ",_("Encrypt"));

  if(flags&PUBKEY_USAGE_AUTH)
    tty_printf("%s ",_("Authenticate"));
}


/* Returns the key flags */
static unsigned int
ask_key_flags(int algo,int subkey)
{
  /* TRANSLATORS: Please use only plain ASCII characters for the
     translation.  If this is not possible use single digits.  Here is
     a description of the fucntions:

       s = Toggle signing capability
       e = Toggle encryption capability
       a = Toggle authentication capability
       q = Finish
  */
  const char *togglers=_("SsEeAaQq");
  char *answer=NULL;
  unsigned int current=0;
  unsigned int possible=openpgp_pk_algo_usage(algo);

  if ( strlen(togglers) != 8 )
    {
      tty_printf ("NOTE: Bad translation at %s:%d. "
                  "Please report.\n", __FILE__, __LINE__);
      togglers = "11223300";
    }

  /* Only primary keys may certify. */
  if(subkey)
    possible&=~PUBKEY_USAGE_CERT;

  /* Preload the current set with the possible set, minus
     authentication, since nobody really uses auth yet. */
  current=possible&~PUBKEY_USAGE_AUTH;

  for(;;)
    {
      tty_printf("\n");
      tty_printf(_("Possible actions for a %s key: "),
		 pubkey_algo_to_string(algo));
      print_key_flags(possible);
      tty_printf("\n");
      tty_printf(_("Current allowed actions: "));
      print_key_flags(current);
      tty_printf("\n\n");

      if(possible&PUBKEY_USAGE_SIG)
	tty_printf(_("   (%c) Toggle the sign capability\n"),
		   togglers[0]);
      if(possible&PUBKEY_USAGE_ENC)
	tty_printf(_("   (%c) Toggle the encrypt capability\n"),
		   togglers[2]);
      if(possible&PUBKEY_USAGE_AUTH)
	tty_printf(_("   (%c) Toggle the authenticate capability\n"),
		   togglers[4]);

      tty_printf(_("   (%c) Finished\n"),togglers[6]);
      tty_printf("\n");

      xfree(answer);
      answer = cpr_get("keygen.flags",_("Your selection? "));
      cpr_kill_prompt();

      if(strlen(answer)>1)
	tty_printf(_("Invalid selection.\n"));
      else if(*answer=='\0' || *answer==togglers[6] || *answer==togglers[7])
	break;
      else if((*answer==togglers[0] || *answer==togglers[1])
	      && possible&PUBKEY_USAGE_SIG)
	{
	  if(current&PUBKEY_USAGE_SIG)
	    current&=~PUBKEY_USAGE_SIG;
	  else
	    current|=PUBKEY_USAGE_SIG;
	}
      else if((*answer==togglers[2] || *answer==togglers[3])
	      && possible&PUBKEY_USAGE_ENC)
	{
	  if(current&PUBKEY_USAGE_ENC)
	    current&=~PUBKEY_USAGE_ENC;
	  else
	    current|=PUBKEY_USAGE_ENC;
	}
      else if((*answer==togglers[4] || *answer==togglers[5])
	      && possible&PUBKEY_USAGE_AUTH)
	{
	  if(current&PUBKEY_USAGE_AUTH)
	    current&=~PUBKEY_USAGE_AUTH;
	  else
	    current|=PUBKEY_USAGE_AUTH;
	}
      else
	tty_printf(_("Invalid selection.\n"));
    }

  xfree(answer);

  return current;
}
#endif



//ROKA - Hard coded to return RSA for key generation

/* Ask for an algorithm.  The function returns the algorithm id to
   create.  If ADDMODE is false the function won't show an option to
   create the primary and subkey combined and won't set R_USAGE
   either.  If a combined algorithm has been selected, the subkey
   algorithm is stored at R_SUBKEY_ALGO.  */
static int
ask_algo (int addmode, int *r_subkey_algo, unsigned int *r_usage)
{
  char *answer;
  int algo;
  int dummy_algo;

  if (!r_subkey_algo)
    r_subkey_algo = &dummy_algo;

/*
    
  fprintf(stderr,("Please select what kind of key you want:\n"));
  if (!addmode)
    fprintf (stderr, ("   (%d) RSA and RSA (default)\n"), 1 );
  if ( !addmode )
    fprintf (stderr,("   (%d) DSA and Elgamal\n"), 2 );

  tty_printf(    _("   (%d) DSA (sign only)\n"), 3 );
  tty_printf(    _("   (%d) RSA (sign only)\n"), 4 );

  if (addmode)
    {
      tty_printf (_("   (%d) Elgamal (encrypt only)\n"), 5 );
      tty_printf (_("   (%d) RSA (encrypt only)\n"), 6 );
    }
  if (opt.expert)
    {
      tty_printf (_("   (%d) DSA (set your own capabilities)\n"), 7 );
      tty_printf (_("   (%d) RSA (set your own capabilities)\n"), 8 );
    }

    
  for (;;)
    {
      *r_usage = 0;
      *r_subkey_algo = 0;
      answer = cpr_get ("keygen.algo", _("Your selection? "));
      cpr_kill_prompt ();
      algo = *answer? atoi(answer): 1;
      xfree (answer);
      if ( algo == 1 && !addmode )
        {
          algo = PUBKEY_ALGO_RSA;
          *r_subkey_algo = PUBKEY_ALGO_RSA;
          break;
	}
      else if (algo == 2 && !addmode)
        {
          algo = PUBKEY_ALGO_DSA;
          *r_subkey_algo = PUBKEY_ALGO_ELGAMAL_E;
          break;
	}
      else if (algo == 3)
        {
          algo = PUBKEY_ALGO_DSA;
          *r_usage = PUBKEY_USAGE_SIG;
          break;
	}
      else if (algo == 4)
        {
          algo = PUBKEY_ALGO_RSA;
          *r_usage = PUBKEY_USAGE_SIG;
          break;
	}
      else if (algo == 5 && addmode)
        {
          algo = PUBKEY_ALGO_ELGAMAL_E;
          *r_usage = PUBKEY_USAGE_ENC;
          break;
	}
      else if (algo == 6 && addmode)
        {
          algo = PUBKEY_ALGO_RSA;
          *r_usage = PUBKEY_USAGE_ENC;
          break;
	}
      else if (algo == 7 && opt.expert)
        {
          algo = PUBKEY_ALGO_DSA;
          *r_usage = ask_key_flags (algo, addmode);
          break;
	}
      else if (algo == 8 && opt.expert)
        {
          algo = PUBKEY_ALGO_RSA;
          *r_usage = ask_key_flags (algo, addmode);
          break;
	}
      else
        tty_printf (_("Invalid selection.\n"));
    }
*/
    
    

        *r_usage = 0;
        *r_subkey_algo = 0;

        algo = PUBKEY_ALGO_RSA;
        *r_subkey_algo = PUBKEY_ALGO_RSA;

  return algo;
}


/* Ask for the key size.  ALGO is the algorithm.  If PRIMARY_KEYSIZE
   is not 0, the function asks for the size of the encryption
   subkey.  */
static unsigned int
ask_keysize (int algo, unsigned int primary_keysize)
{
  unsigned nbits, min, def=2048, max=4096;
  int for_subkey = !!primary_keysize;
  int autocomp = 0;


  min=1024;

  if (primary_keysize)
    {
      /* Deduce the subkey size from the primary key size.  */
       if (algo == PUBKEY_ALGO_DSA && primary_keysize > 3072)
        nbits = 3072; /* For performance reasons we don't support more
                         than 3072 bit DSA.  However we won't see this
                         case anyway because DSA can't be used as an
                         encryption subkey ;-). */
      else
        nbits = primary_keysize;
      autocomp = 1;
      goto leave;
    }

  switch(algo)
    {
    case PUBKEY_ALGO_DSA:
      def=2048;
      max=3072;
      break;

    case PUBKEY_ALGO_RSA:
      min=1024;
      break;
    }

    
    nbits = 4096;


 leave:
  if( algo == PUBKEY_ALGO_DSA && (nbits % 64) )
    {
      nbits = ((nbits + 63) / 64) * 64;

    }
  else if( (nbits % 32) )
    {
      nbits = ((nbits + 31) / 32) * 32;

    }

  return nbits;
}



/****************
 * Parse an expire string and return its value in seconds.
 * Returns (u32)-1 on error.
 * This isn't perfect since scan_isodatestr returns unix time, and
 * OpenPGP actually allows a 32-bit time *plus* a 32-bit offset.
 * Because of this, we only permit setting expirations up to 2106, but
 * OpenPGP could theoretically allow up to 2242.  I think we'll all
 * just cope for the next few years until we get a 64-bit time_t or
 * similar.
 */
u32
parse_expire_string (u32 timestamp, const char *string)
{
    int mult;
    u32 seconds;
    u32 abs_date = 0;
    
    if ( !*string )
        seconds = 0;
    else if ( !strncmp (string, "seconds=", 8) )
        seconds = atoi (string+8);
    else if( (abs_date = scan_isodatestr(string)) && abs_date > timestamp )
        seconds = abs_date - timestamp;
    else if( (mult=check_valid_days(string)) )
        seconds = atoi(string) * 86400L * mult;
    else
        seconds=(u32)-1;
    
    return seconds;
}


/* Parse an Creation-Date string which is either "1986-04-26" or
   "19860426T042640".  Returns 0 on error. */
static u32
parse_creation_string (const char *string)
{
  u32 seconds;

  if (!*string)
    seconds = 0;
  else if ( !strncmp (string, "seconds=", 8) )
    seconds = atoi (string+8);
  else if ( !(seconds = scan_isodatestr (string)))
    seconds = isotime2seconds (string);
  return seconds;
}



/* FIXME: We need a way to cancel this prompt. */
static DEK *
do_ask_passphrase( STRING2KEY **ret_s2k, char *passPhrase )
{
    DEK *dek = NULL;
    STRING2KEY *s2k;
    const char *errtext = NULL;

    fprintf(stderr,"You need a Passphrase to protect your secret key.\n\n") ;

    s2k = xmalloc_secure( sizeof *s2k );
    
    for(;;) {
	s2k->mode = opt.s2k_mode;
	s2k->hash_algo = S2K_DIGEST_ALGO;
    set_next_passphrase( passPhrase );
	dek = passphrase_to_dek( NULL, 0, opt.s2k_cipher_algo, s2k,2,
                                 errtext, NULL);
    if( !dek->keylen ) {
	    xfree(dek); dek = NULL;
	    xfree(s2k); s2k = NULL;
	   // tty_printf(_(
	   // "You don't want a passphrase - this is probably a *bad* idea!\n"
	   // "I will do it anyway.  You can change your passphrase at any time,\n"
	    //"using this program with the option \"--edit-key\".\n\n"));
	    break;
	}
	else
	    break; /* okay */
    }
    *ret_s2k = s2k;
    return dek;
}

static int
do_create( int algo, unsigned int nbits, KBNODE pub_root, KBNODE sec_root,
	   DEK *dek, STRING2KEY *s2k, PKT_secret_key **sk, u32 timestamp,
	   u32 expiredate, int is_subkey )
{
  int rc=0;

  if( !opt.batch )
    fprintf(stderr,
"We need to generate a lot of random bytes. It is a good idea to perform\n"
"some other action (type on the keyboard, move the mouse, utilize the\n"
"disks) during the prime generation; this gives the random number\n"
"generator a better chance to gain enough entropy.\n" );

  if( algo == PUBKEY_ALGO_ELGAMAL_E )
    rc = gen_elg(algo, nbits, pub_root, sec_root, dek, s2k, sk, timestamp,
		 expiredate, is_subkey);
  else if( algo == PUBKEY_ALGO_DSA )
    rc = gen_dsa(nbits, pub_root, sec_root, dek, s2k, sk, timestamp,
		 expiredate, is_subkey);
  else if( algo == PUBKEY_ALGO_RSA )
    rc = gen_rsa(algo, nbits, pub_root, sec_root, dek, s2k, sk, timestamp,
		 expiredate, is_subkey);
  else
    BUG();

  return rc;
}



/****************
 * Generate a new user id packet, or return NULL if canceled
 */
PKT_user_id *
generate_user_id()
{
    PKT_user_id *uid;
    char *p;
    size_t n;

    //ELMO p = ask_user_id( 1 );
    p = NULL; //ELMO
    if( !p )
	return NULL;
    n = strlen(p);
    uid = xmalloc_clear( sizeof *uid + n );
    uid->len = n;
    strcpy(uid->name, p);
    uid->ref = 1;
    return uid;
}



static void
release_parameter_list( struct para_data_s *r )
{
    struct para_data_s *r2;

    for( ; r ; r = r2 ) {
	r2 = r->next;
	if( r->key == pPASSPHRASE_DEK )
	    xfree( r->u.dek );
	else if( r->key == pPASSPHRASE_S2K )
	    xfree( r->u.s2k );

	xfree(r);
    }
}


static struct para_data_s *
get_parameter( struct para_data_s *para, enum para_name key )
{
    struct para_data_s *r;

    for( r = para; r && r->key != key; r = r->next )
	;
    return r;
}

static const char *
get_parameter_value( struct para_data_s *para, enum para_name key )
{
    struct para_data_s *r = get_parameter( para, key );
    return (r && *r->u.value)? r->u.value : NULL;
}

static int
get_parameter_algo( struct para_data_s *para, enum para_name key )
{
    int i;
    struct para_data_s *r = get_parameter( para, key );
    if( !r )
	return -1;
    if( digitp( r->u.value ) )
	i = atoi( r->u.value );
    else
        i = string_to_pubkey_algo( r->u.value );
    if (i == PUBKEY_ALGO_RSA_E || i == PUBKEY_ALGO_RSA_S)
      i = 0; /* we don't want to allow generation of these algorithms */
    return i;
}



/*
 * parse the usage parameter and set the keyflags.  Return true on error.
 */
static int
parse_parameter_usage (const char *fname,
                       struct para_data_s *para, enum para_name key)
{
    struct para_data_s *r = get_parameter( para, key );
    char *p, *pn;
    unsigned int use;

    if( !r )
	return 0; /* none (this is an optional parameter)*/

    use = 0;
    pn = r->u.value;
    while ( (p = strsep (&pn, " \t,")) ) {
        if ( !*p)
            ;
        else if ( !ascii_strcasecmp (p, "sign") )
            use |= PUBKEY_USAGE_SIG;
        else if ( !ascii_strcasecmp (p, "encrypt") )
            use |= PUBKEY_USAGE_ENC;
        else if ( !ascii_strcasecmp (p, "auth") )
            use |= PUBKEY_USAGE_AUTH;
        else {
            log_error("%s:%d: invalid usage list\n", fname, r->lnr );
            return -1; /* error */
        }
    }
    r->u.usage = use;
    return 1;
}



static int
parse_revocation_key (const char *fname,
		      struct para_data_s *para, enum para_name key)
{
  struct para_data_s *r = get_parameter( para, key );
  struct revocation_key revkey;
  char *pn;
  int i;

  if( !r )
    return 0; /* none (this is an optional parameter) */

  pn = r->u.value;

  revkey.class=0x80;
  revkey.algid=atoi(pn);
  if(!revkey.algid)
    goto fail;

  /* Skip to the fpr */
  while(*pn && *pn!=':')
    pn++;

  if(*pn!=':')
    goto fail;

  pn++;

  for(i=0;i<MAX_FINGERPRINT_LEN && *pn;i++,pn+=2)
    {
      int c=hextobyte(pn);
      if(c==-1)
	goto fail;

      revkey.fpr[i]=c;
    }

  /* skip to the tag */
  while(*pn && *pn!='s' && *pn!='S')
    pn++;

  if(ascii_strcasecmp(pn,"sensitive")==0)
    revkey.class|=0x40;

  memcpy(&r->u.revkey,&revkey,sizeof(struct revocation_key));

  return 0;

  fail:
  log_error("%s:%d: invalid revocation key\n", fname, r->lnr );
  return -1; /* error */
}

static u32
get_parameter_u32( struct para_data_s *para, enum para_name key )
{
  struct para_data_s *r;

  r = get_parameter (para, key);
  if (!r && key == pKEYCREATIONDATE)
    {
      /* Return a default for the creation date if it has not yet been
         set.  We need to set this into the parameter list so that a
         second call for pKEYCREATIONDATE returns the same value.  The
         default is the current time unless an explicit creation date
         has been specified.  Checking the creation date here is only
         for the case that it has not yet been parsed. */
      r = get_parameter (para, pCREATIONDATE);
      if (r && *r->u.value)
        {
          u32 seconds;

          seconds = parse_creation_string (r->u.value);
          if (!seconds)
            log_error ("invalid creation date in line %d\n", r->lnr );
          else /* Okay: Change this parameter. */
            {
              r->u.creation = seconds;
              r->key = pKEYCREATIONDATE;
            }
        }

      r = get_parameter (para, key);
      if (!r)
        {
          /* Create a new parameter. */
          r = xmalloc_clear (sizeof *r);
          r->key = key;
          r->u.creation = make_timestamp ();
          r->next = para;
          para = r;
        }

      r = get_parameter (para, key);
      assert (r);
    }


    if (!r)
      return 0;
    if( r->key == pKEYCREATIONDATE )
      return r->u.creation;
    if( r->key == pKEYEXPIRE || r->key == pSUBKEYEXPIRE )
	return r->u.expire;
    if( r->key == pKEYUSAGE || r->key == pSUBKEYUSAGE )
	return r->u.usage;

    return (unsigned int)strtoul( r->u.value, NULL, 10 );
}




static unsigned int
get_parameter_uint( struct para_data_s *para, enum para_name key )
{
    return get_parameter_u32( para, key );
}

static DEK *
get_parameter_dek( struct para_data_s *para, enum para_name key )
{
    struct para_data_s *r = get_parameter( para, key );
    return r? r->u.dek : NULL;
}

static STRING2KEY *
get_parameter_s2k( struct para_data_s *para, enum para_name key )
{
    struct para_data_s *r = get_parameter( para, key );
    return r? r->u.s2k : NULL;
}



static struct revocation_key *
get_parameter_revkey( struct para_data_s *para, enum para_name key )
{
    struct para_data_s *r = get_parameter( para, key );
    return r? &r->u.revkey : NULL;
}





static int
proc_parameter_file( struct para_data_s *para, const char *fname,
                     struct output_control_s *outctrl)
{
  struct para_data_s *r;
  const char *s1, *s2, *s3;
  size_t n;
  char *p;
  int have_user_id=0,err,algo;

  /* Check that we have all required parameters. */
  r = get_parameter( para, pKEYTYPE );
  if(r)
    {
      algo=get_parameter_algo(para,pKEYTYPE);
      if(check_pubkey_algo2(algo,PUBKEY_USAGE_SIG))
	{
	  log_error("%s:%d: invalid algorithm\n", fname, r->lnr );
	  return -1;
	}
    }
  else
    {
      log_error("%s: no Key-Type specified\n",fname);
      return -1;
    }
    
    

    
  err = parse_parameter_usage (fname, para, pKEYUSAGE);
  if (!err)
    {
      /* Default to algo capabilities if key-usage is not provided */
      r = xmalloc_clear(sizeof(*r));
      r->key = pKEYUSAGE;
      r->u.usage = openpgp_pk_algo_usage(algo);
      r->next = para;
      para = r;
    }
  else if (err == -1)
    return -1;
  else
    {
      r = get_parameter (para, pKEYUSAGE);
      if (r && (r->u.usage & ~openpgp_pk_algo_usage (algo)))
        {
          log_error ("%s:%d: specified Key-Usage not allowed for algo %d\n",
                     fname, r->lnr, algo);
          return -1;
        }
    }

    

  r = get_parameter( para, pSUBKEYTYPE );
  if(r)
    {
      algo = get_parameter_algo (para, pSUBKEYTYPE);
      if (check_pubkey_algo (algo))
	{
	  log_error ("%s:%d: invalid algorithm\n", fname, r->lnr );
	  return -1;
	}

      err = parse_parameter_usage (fname, para, pSUBKEYUSAGE);
      if (!err)
	{
	  /* Default to algo capabilities if subkey-usage is not
	     provided */
	  r = xmalloc_clear (sizeof(*r));
	  r->key = pSUBKEYUSAGE;
	  r->u.usage = openpgp_pk_algo_usage (algo);
	  r->next = para;
	  para = r;
	}
      else if (err == -1)
	return -1;
      else
        {
          r = get_parameter (para, pSUBKEYUSAGE);
          if (r && (r->u.usage & ~openpgp_pk_algo_usage (algo)))
            {
              log_error ("%s:%d: specified Subkey-Usage not allowed"
                         " for algo %d\n", fname, r->lnr, algo);
              return -1;
            }
        }
    }
    

  if( get_parameter_value( para, pUSERID ) )
    have_user_id=1;
  else
    {
      /* create the formatted user ID */
      s1 = get_parameter_value( para, pNAMEREAL );
      s2 = get_parameter_value( para, pNAMECOMMENT );
      s3 = get_parameter_value( para, pNAMEEMAIL );
      if( s1 || s2 || s3 )
	{
	  n = (s1?strlen(s1):0) + (s2?strlen(s2):0) + (s3?strlen(s3):0);
	  r = xmalloc_clear( sizeof *r + n + 20 );
	  r->key = pUSERID;
	  p = r->u.value;
	  if( s1 )
	    p = stpcpy(p, s1 );
	  if( s2 )
	    p = stpcpy(stpcpy(stpcpy(p," ("), s2 ),")");
	  if( s3 )
	    p = stpcpy(stpcpy(stpcpy(p," <"), s3 ),">");
	  r->next = para;
	  para = r;
	  have_user_id=1;
	}
    }

  if(!have_user_id)
    {
      log_error("%s: no User-ID specified\n",fname);
      return -1;
    }
    


  /* Set preferences, if any. */
  keygen_set_std_prefs(get_parameter_value( para, pPREFERENCES ), 0);




    
  /* Set revoker, if any. */
  if (parse_revocation_key (fname, para, pREVOKER))
    return -1;

  /* make DEK and S2K from the Passphrase */
  r = get_parameter( para, pPASSPHRASE );
  if( r && *r->u.value ) {
    /* We have a plain text passphrase - create a DEK from it.
     * It is a little bit ridiculous to keep it in secure memory
     * but because we do this alwasy, why not here.  */
    STRING2KEY *s2k;
    DEK *dek;

    s2k = xmalloc_secure( sizeof *s2k );
    s2k->mode = opt.s2k_mode;
    s2k->hash_algo = S2K_DIGEST_ALGO;
    set_next_passphrase( r->u.value );
    dek = passphrase_to_dek( NULL, 0, opt.s2k_cipher_algo, s2k, 2,
			     NULL, NULL);
    set_next_passphrase( NULL );
    assert( dek );
    memset( r->u.value, 0, strlen(r->u.value) );

    r = xmalloc_clear( sizeof *r );
    r->key = pPASSPHRASE_S2K;
    r->u.s2k = s2k;
    r->next = para;
    para = r;
    r = xmalloc_clear( sizeof *r );
    r->key = pPASSPHRASE_DEK;
    r->u.dek = dek;
    r->next = para;
    para = r;
  }


  /* Make KEYCREATIONDATE from Creation-Date.  */
  r = get_parameter (para, pCREATIONDATE);
  if (r && *r->u.value)
    {
      u32 seconds;

      seconds = parse_creation_string (r->u.value);
      if (!seconds)
	{
	  log_error ("%s:%d: invalid creation date\n", fname, r->lnr );
	  return -1;
	}
      r->u.creation = seconds;
      r->key = pKEYCREATIONDATE;  /* Change that entry. */
    }
    

  /* Make KEYEXPIRE from Expire-Date.  */
  r = get_parameter( para, pEXPIREDATE );
  if( r && *r->u.value )
    {
      u32 seconds;

      seconds = parse_expire_string
        (get_parameter_u32 (para, pKEYCREATIONDATE), r->u.value);
      if (seconds == (u32)(-1))
	{
	  log_error("%s:%d: invalid expire date\n", fname, r->lnr );
	  return -1;
	}
      r->u.expire = seconds;
      r->key = pKEYEXPIRE;  /* change hat entry */
      /* also set it for the subkey */
      r = xmalloc_clear( sizeof *r + 20 );
      r->key = pSUBKEYEXPIRE;
      r->u.expire = seconds;
      r->next = para;
      para = r;
    }

    

    
  if( !!outctrl->pub.newfname ^ !!outctrl->sec.newfname ) {
    log_error("%s:%d: only one ring name is set\n", fname, outctrl->lnr );
    return -1;
  }
    
    
  do_generate_keypair (para, outctrl, 0);

    
  return 0;
}



#ifdef ERNIE
/****************
 * Kludge to allow non interactive key generation controlled
 * by a parameter file.
 * Note, that string parameters are expected to be in UTF-8
 */
static void
read_parameter_file( const char *fname )
{
    static struct { const char *name;
		    enum para_name key;
    } keywords[] = {
	{ "Key-Type",       pKEYTYPE},
	{ "Key-Length",     pKEYLENGTH },
	{ "Key-Usage",      pKEYUSAGE },
	{ "Subkey-Type",    pSUBKEYTYPE },
	{ "Subkey-Length",  pSUBKEYLENGTH },
	{ "Subkey-Usage",   pSUBKEYUSAGE },
	{ "Name-Real",      pNAMEREAL },
	{ "Name-Email",     pNAMEEMAIL },
	{ "Name-Comment",   pNAMECOMMENT },
	{ "Expire-Date",    pEXPIREDATE },
	{ "Creation-Date",  pCREATIONDATE },
	{ "Passphrase",     pPASSPHRASE },
	{ "Preferences",    pPREFERENCES },
	{ "Revoker",        pREVOKER },
        { "Handle",         pHANDLE },
	{ "Keyserver",      pKEYSERVER },
	{ NULL, 0 }
    };
    IOBUF fp;
    byte *line;
    unsigned int maxlen, nline;
    char *p;
    int lnr;
    const char *err = NULL;
    struct para_data_s *para, *r;
    int i;
    struct output_control_s outctrl;

    memset( &outctrl, 0, sizeof( outctrl ) );

    if( !fname || !*fname)
      fname = "-";

    fp = iobuf_open (fname);
    if (fp && is_secured_file (iobuf_get_fd (fp)))
      {
        iobuf_close (fp);
        fp = NULL;
        errno = EPERM;
      }
    if (!fp) {
      log_error (_("can't open `%s': %s\n"), fname, strerror(errno) );
      return;
    }
    iobuf_ioctl (fp, 3, 1, NULL); /* No file caching. */

    lnr = 0;
    err = NULL;
    para = NULL;
    maxlen = 1024;
    line = NULL;
    while ( iobuf_read_line (fp, &line, &nline, &maxlen) ) {
	char *keyword, *value;

	lnr++;
	if( !maxlen ) {
	    err = "line too long";
	    break;
	}
	for( p = line; isspace(*(byte*)p); p++ )
	    ;
	if( !*p || *p == '#' )
	    continue;
	keyword = p;
	if( *keyword == '%' ) {
	    for( ; !isspace(*(byte*)p); p++ )
		;
	    if( *p )
		*p++ = 0;
	    for( ; isspace(*(byte*)p); p++ )
		;
	    value = p;
	    trim_trailing_ws( value, strlen(value) );
	    if( !ascii_strcasecmp( keyword, "%echo" ) )
		log_info("%s\n", value );
	    else if( !ascii_strcasecmp( keyword, "%dry-run" ) )
		outctrl.dryrun = 1;
	    else if( !ascii_strcasecmp( keyword, "%commit" ) ) {
		outctrl.lnr = lnr;
		if (proc_parameter_file( para, fname, &outctrl, 0 ))
                  print_status_key_not_created
                    (get_parameter_value (para, pHANDLE));
		release_parameter_list( para );
		para = NULL;
	    }
	    else if( !ascii_strcasecmp( keyword, "%pubring" ) ) {
		if( outctrl.pub.fname && !strcmp( outctrl.pub.fname, value ) )
		    ; /* still the same file - ignore it */
		else {
		    xfree( outctrl.pub.newfname );
		    outctrl.pub.newfname = xstrdup( value );
		    outctrl.use_files = 1;
		}
	    }
	    else if( !ascii_strcasecmp( keyword, "%secring" ) ) {
		if( outctrl.sec.fname && !strcmp( outctrl.sec.fname, value ) )
		    ; /* still the same file - ignore it */
		else {
		   xfree( outctrl.sec.newfname );
		   outctrl.sec.newfname = xstrdup( value );
		   outctrl.use_files = 1;
		}
	    }
	    else
		log_info("skipping control `%s' (%s)\n", keyword, value );


	    continue;
	}


	if( !(p = strchr( p, ':' )) || p == keyword ) {
	    err = "missing colon";
	    break;
	}
	if( *p )
	    *p++ = 0;
	for( ; isspace(*(byte*)p); p++ )
	    ;
	if( !*p ) {
	    err = "missing argument";
	    break;
	}
	value = p;
	trim_trailing_ws( value, strlen(value) );

	for(i=0; keywords[i].name; i++ ) {
	    if( !ascii_strcasecmp( keywords[i].name, keyword ) )
		break;
	}
	if( !keywords[i].name ) {
	    err = "unknown keyword";
	    break;
	}
	if( keywords[i].key != pKEYTYPE && !para ) {
	    err = "parameter block does not start with \"Key-Type\"";
	    break;
	}

	if( keywords[i].key == pKEYTYPE && para ) {
	    outctrl.lnr = lnr;
	    if (proc_parameter_file( para, fname, &outctrl, 0 ))
              print_status_key_not_created
                (get_parameter_value (para, pHANDLE));
	    release_parameter_list( para );
	    para = NULL;
	}
	else {
	    for( r = para; r; r = r->next ) {
		if( r->key == keywords[i].key )
		    break;
	    }
	    if( r ) {
		err = "duplicate keyword";
		break;
	    }
	}
	r = xmalloc_clear( sizeof *r + strlen( value ) );
	r->lnr = lnr;
	r->key = keywords[i].key;
	strcpy( r->u.value, value );
	r->next = para;
	para = r;
    }
    if( err )
	log_error("%s:%d: %s\n", fname, lnr, err );
    else if( iobuf_error (fp) ) {
	log_error("%s:%d: read error\n", fname, lnr);
    }
    else if( para ) {
	outctrl.lnr = lnr;
	if (proc_parameter_file( para, fname, &outctrl, 0 ))
          print_status_key_not_created (get_parameter_value (para, pHANDLE));
    }

    if( outctrl.use_files ) { /* close open streams */
	iobuf_close( outctrl.pub.stream );
	iobuf_close( outctrl.sec.stream );

        /* Must invalidate that ugly cache to actually close it.  */
        if (outctrl.pub.fname)
          iobuf_ioctl (NULL, 2, 0, (char*)outctrl.pub.fname);
        if (outctrl.sec.fname)
          iobuf_ioctl (NULL, 2, 0, (char*)outctrl.sec.fname);

	xfree( outctrl.pub.fname );
	xfree( outctrl.pub.newfname );
	xfree( outctrl.sec.fname );
	xfree( outctrl.sec.newfname );
    }

    release_parameter_list( para );
    iobuf_close (fp);
}


#endif

/*
 * Generate a keypair (fname is only used in batch mode) If
 * CARD_SERIALNO is not NULL the fucntion will create the keys on an
 * OpenPGP Card.  If BACKUP_ENCRYPTION_DIR has been set and
 * CARD_SERIALNO is NOT NULL, the encryption key for the card gets
 * generate in software, imported to the card and a backup file
 * written to directory given by this argument .
 */

/*
void
generate_keypair (const char *fname, const char *card_serialno,
                  const char *backup_encryption_dir)
*/


//ROKA - New generate keypair, only takes a userID and passPhrase
//       to protect the key

void
generate_keypair (const char *userID, const char *passPhrase)

{
  unsigned int nbits;
  char *uid = NULL;
  DEK *dek;
  STRING2KEY *s2k;
  int algo;
  unsigned int use;
  int both = 0;
  u32 expire;
  struct para_data_s *para = NULL;
  struct para_data_s *r;
  struct output_control_s outctrl;

  memset( &outctrl, 0, sizeof( outctrl ) );

    
#ifdef VOLDAMORT    
    outctrl.use_files = 1;
    outctrl.sec.newfname = xstrdup("key.sec");
    outctrl.pub.newfname = xstrdup("key.pub");

  //Set output
    
    else if( !ascii_strcasecmp( keyword, "%pubring" ) ) {
		if( outctrl.pub.fname && !strcmp( outctrl.pub.fname, value ) )
		    ; /* still the same file - ignore it */
		else {
		    xfree( outctrl.pub.newfname );
		    outctrl.pub.newfname = xstrdup( value );
		    outctrl.use_files = 1;
		}
    }
    else if( !ascii_strcasecmp( keyword, "%secring" ) ) {
		if( outctrl.sec.fname && !strcmp( outctrl.sec.fname, value ) )
		    ; /* still the same file - ignore it */
		else {
            xfree( outctrl.sec.newfname );
            outctrl.sec.newfname = xstrdup( value );
            outctrl.use_files = 1;
		}
    }
    
#endif
    
    

      int subkey_algo;

    algo = ask_algo (0, &subkey_algo, &use );


    if (subkey_algo)
        {
          /* Create primary and subkey at once.  */
          both = 1;
          r = xmalloc_clear( sizeof *r + 20 );
          r->key = pKEYTYPE;
          sprintf (r->u.value, "%d", algo);
          r->next = para;
          para = r;
	  nbits = ask_keysize (algo, 0);
	  r = xmalloc_clear( sizeof *r + 20 );
	  r->key = pKEYLENGTH;
	  sprintf( r->u.value, "%u", nbits);
	  r->next = para;
	  para = r;
          r = xmalloc_clear( sizeof *r + 20 );
          r->key = pKEYUSAGE;
          strcpy( r->u.value, "sign" );
          r->next = para;
          para = r;

          r = xmalloc_clear( sizeof *r + 20 );
          r->key = pSUBKEYTYPE;
          sprintf( r->u.value, "%d", subkey_algo );
          r->next = para;
          para = r;
          r = xmalloc_clear( sizeof *r + 20 );
          r->key = pSUBKEYUSAGE;
          strcpy( r->u.value, "encrypt" );
          r->next = para;
          para = r;
        }
      else
        {
          r = xmalloc_clear( sizeof *r + 20 );
          r->key = pKEYTYPE;
          sprintf( r->u.value, "%d", algo );
          r->next = para;
          para = r;

          if (use)
            {
              r = xmalloc_clear( sizeof *r + 25 );
              r->key = pKEYUSAGE;
              sprintf( r->u.value, "%s%s%s",
                       (use & PUBKEY_USAGE_SIG)? "sign ":"",
                       (use & PUBKEY_USAGE_ENC)? "encrypt ":"",
                       (use & PUBKEY_USAGE_AUTH)? "auth":"" );
              r->next = para;
              para = r;
            }
          nbits = 0;
        }

      nbits = ask_keysize (both? subkey_algo : algo, nbits);
      r = xmalloc_clear( sizeof *r + 20 );
      r->key = both? pSUBKEYLENGTH : pKEYLENGTH;
      sprintf( r->u.value, "%u", nbits);
      r->next = para;
      para = r;
    

    expire = 0; //Never expire
    
  r = xmalloc_clear( sizeof *r + 20 );
  r->key = pKEYEXPIRE;
  r->u.expire = expire;
  r->next = para;
  para = r;
  r = xmalloc_clear( sizeof *r + 20 );
  r->key = pSUBKEYEXPIRE;
  r->u.expire = expire;
  r->next = para;
  para = r;

  uid = (char *) userID;
  if( !uid )
    {
      return;
    }
    

  r = xmalloc_clear( sizeof *r + strlen(uid) );
  r->key = pUSERID;
  strcpy( r->u.value, uid );
  r->next = para;
  para = r;
    
  dek = do_ask_passphrase( &s2k ,(char *)passPhrase);
  if( dek )
    {
      r = xmalloc_clear( sizeof *r );
      r->key = pPASSPHRASE_DEK;
      r->u.dek = dek;
      r->next = para;
      para = r;
      r = xmalloc_clear( sizeof *r );
      r->key = pPASSPHRASE_S2K;
      r->u.s2k = s2k;
      r->next = para;
      para = r;
    }


  proc_parameter_file( para, "[internal]", &outctrl);
  release_parameter_list( para );

    
}

/* Create and delete a dummy packet to start off a list of kbnodes. */
static void
start_tree(KBNODE *tree)
{
    PACKET *pkt;

    pkt=xmalloc_clear(sizeof(*pkt));
    pkt->pkttype=PKT_NONE;
    *tree=new_kbnode(pkt);
    delete_kbnode(*tree);

}

static void
do_generate_keypair (struct para_data_s *para,struct output_control_s *outctrl,
                     int card)
{
    KBNODE pub_root = NULL;
    KBNODE sec_root = NULL;
    PKT_secret_key *pri_sk = NULL, *sub_sk = NULL;
    const char *s;
    struct revocation_key *revkey;
    int rc;
    int did_sub = 0;
    u32 timestamp;
    


    if( outctrl->use_files ) {
        
        

        if( outctrl->pub.newfname ) {
            iobuf_close(outctrl->pub.stream);
            outctrl->pub.stream = NULL;
            if (outctrl->pub.fname)
                iobuf_ioctl (NULL, 2, 0, (char*)outctrl->pub.fname);
            xfree( outctrl->pub.fname );
            outctrl->pub.fname =  outctrl->pub.newfname;
            outctrl->pub.newfname = NULL;
            
            if (is_secured_filename (outctrl->pub.fname) ) {
                outctrl->pub.stream = NULL;
                errno = EPERM;
            }
            else
                outctrl->pub.stream = iobuf_create( outctrl->pub.fname );
            if( !outctrl->pub.stream ) {
                fprintf(stderr,"can't create `%s': %s\n", outctrl->pub.newfname,
                          strerror(errno) );
                return;
            }
            if( opt.armor ) {
                outctrl->pub.afx.what = 1;
                iobuf_push_filter( outctrl->pub.stream, armor_filter,
                                  &outctrl->pub.afx );
            }
        }
        if( outctrl->sec.newfname ) {
            mode_t oldmask;
            
            iobuf_close(outctrl->sec.stream);
            outctrl->sec.stream = NULL;
            if (outctrl->sec.fname)
                iobuf_ioctl (NULL, 2, 0, (char*)outctrl->sec.fname);
            xfree( outctrl->sec.fname );
            outctrl->sec.fname =  outctrl->sec.newfname;
            outctrl->sec.newfname = NULL;
            
            oldmask = umask (077);
            if (is_secured_filename (outctrl->sec.fname) ) {
                outctrl->sec.stream = NULL;
                errno = EPERM;
            }
            else
                outctrl->sec.stream = iobuf_create( outctrl->sec.fname );
            umask (oldmask);
            if( !outctrl->sec.stream ) {
                fprintf(stderr,"can't create `%s': %s\n", outctrl->sec.newfname,
                          strerror(errno) );
                return;
            }
            if( opt.armor ) {
                outctrl->sec.afx.what = 5;
                iobuf_push_filter( outctrl->sec.stream, armor_filter,
                                  &outctrl->sec.afx );
            }
        }
        assert( outctrl->pub.stream );
        assert( outctrl->sec.stream );
        if( opt.verbose ) {
            fprintf(stderr,"writing public key to `%s'\n", outctrl->pub.fname );
            if (card)
                fprintf(stderr,"writing secret key stub to `%s'\n",
                          outctrl->sec.fname);
            else
                fprintf(stderr,"writing secret key to `%s'\n", outctrl->sec.fname );
        }
        
    }
    

    

    /* We create the packets as a tree of kbnodes. Because the
     * structure we create is known in advance we simply generate a
     * linked list.  The first packet is a dummy packet which we flag
     * as deleted.  The very first packet must always be a KEY packet.
     */
    
    start_tree(&pub_root);
    start_tree(&sec_root);
    
    timestamp = get_parameter_u32 (para, pKEYCREATIONDATE);
    
    /* Note that, depending on the backend (i.e. the used scdaemon
     version or the internal code), the card key generation may
     update TIMESTAMP for each key.  Thus we need to pass TIMESTAMP
     to all signing function to make sure that the binding signature
     is done using the timestamp of the corresponding (sub)key and
     not that of the primary key.  An alternative implementation
     could tell the signing function the node of the subkey but that
     is more work than just to pass the current timestamp.  */

        rc = do_create( get_parameter_algo( para, pKEYTYPE ),
                       get_parameter_uint( para, pKEYLENGTH ),
                       pub_root, sec_root,
                       get_parameter_dek( para, pPASSPHRASE_DEK ),
                       get_parameter_s2k( para, pPASSPHRASE_S2K ),
                       &pri_sk,
                       timestamp,
                       get_parameter_u32( para, pKEYEXPIRE ), 0 );

    

  
    if(!rc && (revkey=get_parameter_revkey(para,pREVOKER)))
    {
        rc = write_direct_sig (pub_root, pub_root, pri_sk, revkey, timestamp);
        if (!rc)
            write_direct_sig (sec_root, pub_root, pri_sk, revkey, timestamp);
    }
    
    
    if( !rc && (s=get_parameter_value(para, pUSERID)) )
    {
        write_uid(pub_root, s );
        if( !rc )
            write_uid(sec_root, s );
        
        if (!rc)
            rc = write_selfsigs (sec_root, pub_root, pri_sk,
                                 get_parameter_uint (para, pKEYUSAGE),
                                 timestamp);
    }
    
    

    
    


    if( !rc && get_parameter( para, pSUBKEYTYPE ) )
    {
        if (!card)
        {
            rc = do_create( get_parameter_algo( para, pSUBKEYTYPE ),
                           get_parameter_uint( para, pSUBKEYLENGTH ),
                           pub_root, sec_root,
                           get_parameter_dek( para, pPASSPHRASE_DEK ),
                           get_parameter_s2k( para, pPASSPHRASE_S2K ),
                           &sub_sk,
                           timestamp,
                           get_parameter_u32( para, pSUBKEYEXPIRE ), 1 );
        }

        
        if( !rc )
            rc = write_keybinding (pub_root, pub_root, pri_sk, sub_sk,
                                   get_parameter_uint (para, pSUBKEYUSAGE),
                                   timestamp );
        if( !rc )
            rc = write_keybinding (sec_root, pub_root, pri_sk, sub_sk,
                                   get_parameter_uint (para, pSUBKEYUSAGE),
                                   timestamp);
        did_sub = 1;
    }
    

    
    if( !rc && outctrl->use_files ) { /* direct write to specified files */
        rc = write_keyblock( outctrl->pub.stream, pub_root );
        if( rc ){
            log_error("can't write public key: %s\n", g10_errstr(rc) );
        }
        if( !rc ) {
            
            rc = write_keyblock( outctrl->sec.stream, sec_root );
            if( rc ){
                log_error("can't write secret key: %s\n", g10_errstr(rc) );
            }
        }
        
        
        
        
    }
    else if( !rc ) { /* write to the standard keyrings */
        KEYDB_HANDLE pub_hd = keydb_new (0);
        KEYDB_HANDLE sec_hd = keydb_new (1);
        
        /* FIXME: we may have to create the keyring first */
        rc = keydb_locate_writable (pub_hd, NULL);
        if (rc)
    	    fprintf(stderr,"no writable public keyring found: %s\n",
                       g10_errstr (rc));
        
        if (!rc) {
            rc = keydb_locate_writable (sec_hd, NULL);
            if (rc)
                fprintf(stderr,"no writable secret keyring found: %s\n",
                           g10_errstr (rc));
        }
        
        if (!rc && opt.verbose) {
            fprintf(stderr,"writing public key to `%s'\n",
                     keydb_get_resource_name (pub_hd));
            if (card)
                fprintf(stderr,"writing secret key stub to `%s'\n",
                          keydb_get_resource_name (sec_hd));
            else
                fprintf(stderr,"writing secret key to `%s'\n",
                         keydb_get_resource_name (sec_hd));
        }
        
        if (!rc) {
            rc = keydb_insert_keyblock (pub_hd, pub_root);
            if (rc)
                fprintf(stderr,"error writing public keyring `%s': %s\n",
                           keydb_get_resource_name (pub_hd), g10_errstr(rc));
        }
        
        if (!rc) {
            rc = keydb_insert_keyblock (sec_hd, sec_root);
            if (rc)
                fprintf(stderr,"error writing secret keyring `%s': %s\n",
                           keydb_get_resource_name (pub_hd), g10_errstr(rc));
        }
        
        keydb_release (pub_hd);
        keydb_release (sec_hd);
        
        if (!rc) {
            int no_enc_rsa =
            get_parameter_algo(para, pKEYTYPE) == PUBKEY_ALGO_RSA
            && get_parameter_uint( para, pKEYUSAGE )
            && !(get_parameter_uint( para,pKEYUSAGE) & PUBKEY_USAGE_ENC);
            PKT_public_key *pk = find_kbnode (pub_root,
                                              PKT_PUBLIC_KEY)->pkt->pkt.public_key;
            
            keyid_from_pk(pk,pk->main_keyid);
            register_trusted_keyid(pk->main_keyid);
            
            
            update_ownertrust (pk,
                               ((get_ownertrust (pk) & ~TRUST_MASK)
                                | TRUST_ULTIMATE ));
            
            if (!opt.batch) {
                fprintf(stderr,"public and secret key created and signed.\n");
                fprintf(stderr,"\n");
                list_keyblock(pub_root,0,1,NULL);
            }
            
            
            if( !opt.batch
               && ( get_parameter_algo( para, pKEYTYPE ) == PUBKEY_ALGO_DSA
                   || no_enc_rsa )
               && !get_parameter( para, pSUBKEYTYPE ) )
            {
                fprintf(stderr,"Note that this key cannot be used for "
                             "encryption.  You may want to use\n"
                             "the command \"--edit-key\" to generate a "
                             "subkey for this purpose.\n" );
            }
        }
    }
    
    if( rc ) {
        if( opt.batch )
            log_error("key generation failed: %s\n", g10_errstr(rc) );
        else
            fprintf(stderr,"Key generation failed: %s\n", g10_errstr(rc) );
        print_status_key_not_created ( get_parameter_value (para, pHANDLE) );
    }
    else {
        PKT_public_key *pk = find_kbnode (pub_root,
                                          PKT_PUBLIC_KEY)->pkt->pkt.public_key;
        print_status_key_created (did_sub? 'B':'P', pk,
                                  get_parameter_value (para, pHANDLE));
    }
    
    
    release_kbnode( pub_root );
    release_kbnode( sec_root );
    
    if( pri_sk && !card) /* the unprotected  secret key unless we have a */
        free_secret_key(pri_sk); /* shallow copy in card mode. */
    if( sub_sk )
        free_secret_key(sub_sk);
    
    

}

#ifdef ELMO
/****************
 * add a new subkey to an existing key.
 * Returns true if a new key has been generated and put into the keyblocks.
 */
int
generate_subkeypair( KBNODE pub_keyblock, KBNODE sec_keyblock )
{
    int okay=0, rc=0;
    KBNODE node;
    PKT_secret_key *pri_sk = NULL, *sub_sk = NULL;
    int algo;
    unsigned int use;
    u32 expire;
    unsigned nbits;
    char *passphrase = NULL;
    DEK *dek = NULL;
    STRING2KEY *s2k = NULL;
    u32 timestamp;
    int ask_pass = 0;
    
    /* break out the primary secret key */
    node = find_kbnode( sec_keyblock, PKT_SECRET_KEY );
    if( !node ) {
        log_error("Oops; secret key not found anymore!\n");
        goto leave;
    }
    
    /* make a copy of the sk to keep the protected one in the keyblock */
    pri_sk = copy_secret_key( NULL, node->pkt->pkt.secret_key );
    
    timestamp = make_timestamp();
    if( pri_sk->timestamp > timestamp ) {
        ulong d = pri_sk->timestamp - timestamp;
        log_info( d==1 ? _("key has been created %lu second "
                           "in future (time warp or clock problem)\n")
                 : _("key has been created %lu seconds "
                     "in future (time warp or clock problem)\n"), d );
        if( !opt.ignore_time_conflict ) {
            rc = G10ERR_TIME_CONFLICT;
            goto leave;
        }
    }
    
    if (pri_sk->version < 4) {
        log_info (_("NOTE: creating subkeys for v3 keys "
                    "is not OpenPGP compliant\n"));
        goto leave;
    }
    
    if (pri_sk->is_protected && pri_sk->protect.s2k.mode == 1001) {
        tty_printf(_("Secret parts of primary key are not available.\n"));
        rc = G10ERR_NO_SECKEY;
        goto leave;
    }
    
    
    /* Unprotect to get the passphrase.  */
    switch( is_secret_key_protected( pri_sk ) ) {
        case -1:
            rc = G10ERR_PUBKEY_ALGO;
            break;
        case 0:
            tty_printf(_("This key is not protected.\n"));
            break;
        case -2:
            tty_printf(_("Secret parts of primary key are stored on-card.\n"));
            ask_pass = 1;
            break;
        default:
            tty_printf(_("Key is protected.\n"));
            rc = check_secret_key( pri_sk, 0 );
            if( !rc )
                passphrase = get_last_passphrase();
            break;
    }
    if( rc )
        goto leave;
    
    algo = ask_algo (1, NULL, &use);
    assert(algo);
    nbits = ask_keysize (algo, 0);
    expire = ask_expire_interval(timestamp,0,NULL);
    if( !cpr_enabled() && !cpr_get_answer_is_yes("keygen.sub.okay",
                                                 _("Really create? (y/N) ")))
        goto leave;
    
    if (ask_pass)
        dek = do_ask_passphrase (&s2k);
    else if (passphrase) {
        s2k = xmalloc_secure( sizeof *s2k );
        s2k->mode = opt.s2k_mode;
        s2k->hash_algo = S2K_DIGEST_ALGO;
        set_next_passphrase( passphrase );
        dek = passphrase_to_dek( NULL, 0, opt.s2k_cipher_algo, s2k, 2,
                                NULL, NULL );
    }
    
    rc = do_create (algo, nbits, pub_keyblock, sec_keyblock,
                    dek, s2k, &sub_sk, timestamp, expire, 1 );
    if (!rc)
        rc = write_keybinding (pub_keyblock, pub_keyblock, pri_sk, sub_sk,
                               use, timestamp);
    if (!rc)
        rc = write_keybinding (sec_keyblock, pub_keyblock, pri_sk, sub_sk,
                               use, timestamp);
    if (!rc)
    {
        okay = 1;
        //write_status_text (STATUS_KEY_CREATED, "S");
    }
    
leave:
    if( rc )
        log_error(_("Key generation failed: %s\n"), g10_errstr(rc) );
    xfree( passphrase );
    xfree( dek );
    xfree( s2k );
    /* release the copy of the (now unprotected) secret keys */
    if( pri_sk )
        free_secret_key(pri_sk);
    if( sub_sk )
        free_secret_key(sub_sk);
    set_next_passphrase( NULL );
    return okay;
}

#endif  //ELMO


