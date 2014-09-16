/* passphrase.c -  Get a passphrase
 * Copyright (C) 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005,
 *               2006 Free Software Foundation, Inc.
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

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#ifdef ENABLE_AGENT_SUPPORT
# if !defined(HAVE_DOSISH_SYSTEM) && !defined(__riscos__)
#  include <sys/socket.h>
#  include <sys/un.h>
# endif
#endif
#if defined (_WIN32)
#include <windows.h>
#endif
#include <errno.h>
#ifdef HAVE_LOCALE_H
#include <locale.h>
#endif
#ifdef HAVE_LANGINFO_CODESET
#include <langinfo.h>
#endif

#include "util.h"
#include "memory.h"
#include "options.h"
//#include "ttyio.h"
#include "cipher.h"
#include "keydb.h"
#include "main.h"
#include "i18n.h"
#include "status.h"
#ifdef ENABLE_AGENT_SUPPORT
#include "assuan.h"
#endif /*ENABLE_AGENT_SUPPORT*/

static char *fd_passwd = NULL;
static char *next_pw = NULL;
static char *last_pw = NULL;

static void hash_passphrase( DEK *dek, char *pw, STRING2KEY *s2k, int create );



/* Here's an interesting question: since this passphrase was passed in
 on the command line, is there really any point in using secure
 memory for it?  I'm going with 'yes', since it doesn't hurt, and
 might help in some small way (swapping). */

void
set_passphrase_from_string(const char *pass)
{
    xfree( fd_passwd );
    fd_passwd = xmalloc_secure(strlen(pass)+1);
    strcpy(fd_passwd,pass);
}





int
have_static_passphrase()
{
    if ( opt.use_agent )
        return 0;
    return !!fd_passwd;
}

/****************
 * Set the passphrase to be used for the next query and only for the next
 * one.
 */
void
set_next_passphrase( const char *s )
{
    xfree(next_pw);
    next_pw = NULL;
    if( s ) {
	next_pw = xmalloc_secure( strlen(s)+1 );
	strcpy(next_pw, s );
    }
}

/****************
 * Get the last passphrase used in passphrase_to_dek.
 * Note: This removes the passphrase from this modules and
 * the caller must free the result.  May return NULL:
 */
char *
get_last_passphrase()
{
    char *p = last_pw;
    last_pw = NULL;
    return p;
}

/* As if we had used the passphrase - make it the last_pw. */
void
next_to_last_passphrase(void)
{
  if(next_pw)
    {
      last_pw=next_pw;
      next_pw=NULL;
    }
}

#ifdef ERNIE
void
read_passphrase_from_fd( int fd )
{
  int i, len;
  char *pw;

  if ( opt.use_agent )
    { /* Not used but we have to do a dummy read, so that it won't end
         up at the begin of the message if the quite usual trick to
         prepend the passphtrase to the message is used. */
      char buf[1];

      while (!(read (fd, buf, 1) != 1 || *buf == '\n' ))
        ;
      *buf = 0;
      return;
    }

  if (!opt.batch && !opt.quiet)
	fprintf(stderr,"Reading passphrase from file descriptor %d ...", fd );
  for (pw = NULL, i = len = 100; ; i++ )
    {
      if (i >= len-1 )
        {
          char *pw2 = pw;
          len += 100;
          pw = xmalloc_secure( len );
          if( pw2 )
            {
              memcpy(pw, pw2, i );
              xfree (pw2);
            }
          else
            i=0;
	}
      if (read( fd, pw+i, 1) != 1 || pw[i] == '\n' )
        break;
    }
  pw[i] = 0;
  if (!opt.batch)
    fprintf(stderr,"\b\b\b   \n" );

  xfree( fd_passwd );
  fd_passwd = pw;
}








/* Copy the text ATEXT into the buffer P and do plus '+' and percent
   escaping.  Note that the provided buffer needs to be 3 times the
   size of ATEXT plus 1.  Returns a pointer to the leading Nul in P. */
#ifdef ENABLE_AGENT_SUPPORT
static char *
percent_plus_escape (char *p, const char *atext)
{
  const unsigned char *s;

  for (s=atext; *s; s++)
    {
      if (*s < ' ' || *s == '+')
        {
          sprintf (p, "%%%02X", *s);
          p += 3;
        }
      else if (*s == ' ')
        *p++ = '+';
      else
        *p++ = *s;
    }
  *p = 0;
  return p;
}
#endif /*ENABLE_AGENT_SUPPORT*/


#ifdef ENABLE_AGENT_SUPPORT

/* Object for the agent_okay_cb function.  */
struct agent_okay_cb_s {
  char *pw;
};

/* A callback used to get the passphrase from the okay line.  See
   agent-get_passphrase for details.  LINE is the rest of the OK
   status line without leading white spaces. */
static assuan_error_t
agent_okay_cb (void *opaque, const char *line)
{
  struct agent_okay_cb_s *parm = opaque;
  int i;

  /* Note: If the malloc below fails we won't be able to wipe the
     memory at LINE given the current implementation of the Assuan
     code. There is no easy ay around this w/o adding a lot of more
     memory function code to allow wiping arbitrary stuff on memory
     failure. */
  parm->pw = xmalloc_secure (strlen (line)/2+2);

  for (i=0; hexdigitp (line) && hexdigitp (line+1); line += 2)
    parm->pw[i++] = xtoi_2 (line);
  parm->pw[i] = 0;
  return 0;
}
#endif /*ENABLE_AGENT_SUPPORT*/

#endif


/*
 * Clear the cached passphrase.  If CACHEID is not NULL, it will be
 * used instead of a cache ID derived from KEYID.
 */
void
passphrase_clear_cache ( u32 *keyid, const char *cacheid, int algo )
{
#ifdef ENABLE_AGENT_SUPPORT
  assuan_context_t ctx = NULL;
  PKT_public_key *pk;
  byte fpr[MAX_FINGERPRINT_LEN];

#if MAX_FINGERPRINT_LEN < 20
#error agent needs a 20 byte fingerprint
#endif

  if (!opt.use_agent)
    return;

  if (!cacheid)
    {
      pk = xcalloc (1, sizeof *pk);
      memset (fpr, 0, MAX_FINGERPRINT_LEN );
      if( !keyid || get_pubkey( pk, keyid ) )
        {
          goto failure; /* oops: no key for some reason */
        }

      {
        size_t dummy;
        fingerprint_from_pk( pk, fpr, &dummy );
      }
    }
  else
    pk = NULL;

  if ( !(ctx = agent_open (0, NULL)) )
    goto failure;

  {
      char *line, *p;
      int i, rc;

      if (cacheid)
        {
          line = xmalloc (17 + 3*strlen (cacheid) + 2);
          strcpy (line, "CLEAR_PASSPHRASE ");
          p = line+17;
          p = percent_plus_escape (p, cacheid);
        }
      else
        {
          line = xmalloc (17 + 40 + 2);
          strcpy (line, "CLEAR_PASSPHRASE ");
          p = line+17;
          for (i=0; i < 20; i++, p +=2 )
            sprintf (p, "%02X", fpr[i]);
        }
      *p = 0;

      rc = assuan_transact (ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
      xfree (line);
      if (rc)
        {
          log_error (_("problem with the agent - disabling agent use\n"));
          opt.use_agent = 0;
        }
    }

 failure:
  agent_close (ctx);
  if (pk)
    free_public_key( pk );
#endif /*ENABLE_AGENT_SUPPORT*/
}

#ifdef ERNIE
/****************
 * Ask for a passphrase and return that string.
 */
char *
ask_passphrase (const char *description,
                const char *tryagain_text,
                const char *promptid,
                const char *prompt,
                const char *cacheid, int *canceled)
{
  char *pw = NULL;

  if (canceled)
    *canceled = 0;

  if (!opt.batch && description)
    {
      if (strchr (description, '%'))
        {
          char *tmp = unescape_percent_string (description);
          tty_printf ("\n%s\n", tmp);
          xfree (tmp);
        }
      else
        tty_printf ("\n%s\n",description);
    }

 agent_died:
  if ( opt.use_agent )
    {
      pw = agent_get_passphrase (NULL, 0, cacheid,
                                 tryagain_text, description, prompt,
                                 canceled );
      if (!pw)
        {
          if (!opt.use_agent)
            goto agent_died;
          pw = NULL;
        }
    }
  else if (fd_passwd)
    {
      pw = xmalloc_secure (strlen(fd_passwd)+1);
      strcpy (pw, fd_passwd);
    }
  else if (opt.batch)
    {
      fprintf(stderr,"can't query passphrase in batch mode\n");
      pw = NULL;
    }
  else {
    if (tryagain_text)
      fprintf(stderr,"%s.\n", tryagain_text);
    pw = cpr_get_hidden(promptid? promptid : "passphrase.ask",
                        prompt?prompt : _("Enter passphrase: ") );
    tty_kill_prompt();
  }

  if (!pw || !*pw)
    write_status( STATUS_MISSING_PASSPHRASE );

  return pw;
}
#endif

/* Return a new DEK object Using the string-to-key sepcifier S2K.  Use
 * KEYID and PUBKEY_ALGO to prompt the user.

   MODE 0:  Allow cached passphrase
        1:  Ignore cached passphrase
        2:  Ditto, but change the text to "repeat entry"
*/
DEK *
passphrase_to_dek(u32 *keyid, int pubkey_algo,
		   int cipher_algo, STRING2KEY *s2k, int mode,
                   const char *tryagain_text, int *canceled)
{
    char *pw = NULL;
    DEK *dek;
    STRING2KEY help_s2k;

    

    if (canceled)
      *canceled = 0;

    if( !s2k ) {
        /* This is used for the old rfc1991 mode
         * Note: This must match the code in encode.c with opt.rfc1991 set */
	s2k = &help_s2k;
	s2k->mode = 0;
	s2k->hash_algo = S2K_DIGEST_ALGO;
    }

    /* If we do not have a passphrase available in NEXT_PW and status
       information are request, we print them now. */
    
#ifdef ERNIE
    
    //if( !next_pw && is_status_enabled() ) {
    if(!next_pw && 1){ //is_status_enabled == 1
	char buf[50];

	if( keyid ) {
            u32 used_kid[2];
            char *us;

	    if( keyid[2] && keyid[3] ) {
                used_kid[0] = keyid[2];
                used_kid[1] = keyid[3];
            }
            else {
                used_kid[0] = keyid[0];
                used_kid[1] = keyid[1];
            }

           // us = get_long_user_id_string( keyid );
           // write_status_text( STATUS_USERID_HINT, us );
            xfree(us);

	    sprintf( buf, "%08lX%08lX %08lX%08lX %d 0",
                     (ulong)keyid[0], (ulong)keyid[1],
                     (ulong)used_kid[0], (ulong)used_kid[1],
                     pubkey_algo );

	    //write_status_text( STATUS_NEED_PASSPHRASE, buf );
	}
	else {
	    sprintf( buf, "%d %d %d", cipher_algo, s2k->mode, s2k->hash_algo );
	    //write_status_text( STATUS_NEED_PASSPHRASE_SYM, buf );
        fprintf(stderr,"%s",buf);
	}
        
        
    }
    

    /* If we do have a keyID, we do not have a passphrase available in
       NEXT_PW, we are not running in batch mode and we do not want to
       ignore the passphrase cache (mode!=1), print a prompt with
       information on that key. */
    if( keyid && !opt.batch && !next_pw && mode!=1 ) {
	PKT_public_key *pk = xmalloc_clear( sizeof *pk );
	char *p;

	p=get_user_id_native(keyid);
	tty_printf("\n");
	tty_printf(_("You need a passphrase to unlock the secret key for\n"
		     "user: \"%s\"\n"),p);
	xfree(p);

	if( !get_pubkey( pk, keyid ) ) {
	    const char *s = pubkey_algo_to_string( pk->pubkey_algo );
	    tty_printf( _("%u-bit %s key, ID %s, created %s"),
		       nbits_from_pk( pk ), s?s:"?", keystr(keyid),
		       strtimestamp(pk->timestamp) );
	    if( keyid[2] && keyid[3] && keyid[0] != keyid[2]
				     && keyid[1] != keyid[3] )
	      {
		if(keystrlen()>10)
		  {
		    tty_printf("\n");
		    tty_printf(_("         (subkey on main key ID %s)"),
			       keystr(&keyid[2]) );
		  }
		else
		  tty_printf( _(" (main key ID %s)"), keystr(&keyid[2]) );
	      }
	    tty_printf("\n");
	}

	tty_printf("\n");
        if (pk)
          free_public_key( pk );
    }

 agent_died:
    if( next_pw ) {
        /* Simply return the passphrase we already have in NEXT_PW. */
	pw = next_pw;
	next_pw = NULL;
    }
    else if ( opt.use_agent ) {
      /* Divert to the gpg-agent. */
        pw = agent_get_passphrase ( keyid, mode == 2? 1: 0, NULL,
                                    tryagain_text, NULL, NULL, canceled );
        if (!pw)
          {
            if (!opt.use_agent)
              goto agent_died;
            pw = xstrdup ("");
          }
        if( *pw && mode == 2 )
	  {
	    int i;
	    for(i=0;i<opt.passwd_repeat;i++)
	      {
		char *pw2 = agent_get_passphrase ( keyid, 2, NULL, NULL, NULL,
						   NULL, canceled );
		if (!pw2)
		  {
		    if (!opt.use_agent)
		      {
			xfree (pw);
			pw = NULL;
			goto agent_died;
		      }
		    pw2 = xstrdup ("");
		  }
		if( strcmp(pw, pw2) )
		  {
		    xfree(pw2);
		    xfree(pw);
		    return NULL;
		  }
		xfree(pw2);
	      }
	  }
    }
    else if( fd_passwd ) {
        /* Return the passphrase we have store in FD_PASSWD. */
	pw = xmalloc_secure( strlen(fd_passwd)+1 );
	strcpy( pw, fd_passwd );
    }
    else if( opt.batch )
      {
	log_error(_("can't query passphrase in batch mode\n"));
	pw = xstrdup( "" ); /* return an empty passphrase */
      }
    else {
        /* Read the passphrase from the tty or the command-fd. */
	pw = cpr_get_hidden("passphrase.enter", _("Enter passphrase: ") );
	tty_kill_prompt();
	if( mode == 2 && !cpr_enabled() )
	  {
	    int i;
	    for(i=0;i<opt.passwd_repeat;i++)
	      {
		char *pw2 = cpr_get_hidden("passphrase.repeat",
					   _("Repeat passphrase: ") );
		tty_kill_prompt();
		if( strcmp(pw, pw2) )
		  {
		    xfree(pw2);
		    xfree(pw);
		    return NULL;
		  }
		xfree(pw2);
	      }
	  }
    }

#endif
    
    //pw = xmalloc_secure( strlen(passPhrase)+1 );
    //strcpy( pw, passPhrase );
    
    pw = next_pw;
    
    if( !pw || !*pw ){
	 fprintf(stderr,"Missing Passphrase for private key");
    }
        
    /* Hash the passphrase and store it in a newly allocated DEK
       object.  Keep a copy of the passphrase in LAST_PW for use by
       get_last_passphrase(). */
    dek = xmalloc_secure_clear ( sizeof *dek );
    dek->algo = cipher_algo;
    if( (!pw || !*pw) && mode == 2 )
	dek->keylen = 0;
    else
	hash_passphrase( dek, pw, s2k, mode==2 );
    //xfree(last_pw); //DUMBO
    last_pw = pw;

    
    return dek;
}


/****************
 * Hash a passphrase using the supplied s2k. If create is true, create
 * a new salt or what else must be filled into the s2k for a new key.
 * always needs: dek->algo, s2k->mode, s2k->hash_algo.
 */
static void
hash_passphrase( DEK *dek, char *pw, STRING2KEY *s2k, int create )
{
    MD_HANDLE md;
    int pass, i;
    int used = 0;
    int pwlen = strlen(pw);

    assert( s2k->hash_algo );
    dek->keylen = cipher_get_keylen( dek->algo ) / 8;
    if( !(dek->keylen > 0 && dek->keylen <= DIM(dek->key)) ){
        fprintf(stderr,"Horrid Bug\n");
        exit(3);
    }
	
    md = md_open( s2k->hash_algo, 1);
    for(pass=0; used < dek->keylen ; pass++ ) {
	if( pass ) {
            md_reset(md);
	    for(i=0; i < pass; i++ ) /* preset the hash context */
		md_putc(md, 0 );
	}

	if( s2k->mode == 1 || s2k->mode == 3 ) {
	    int len2 = pwlen + 8;
	    ulong count = len2;

	    if( create && !pass ) {
		randomize_buffer(s2k->salt, 8, 1);
		if( s2k->mode == 3 )
		    s2k->count = opt.s2k_count;
	    }

	    if( s2k->mode == 3 ) {
		count = S2K_DECODE_COUNT(s2k->count);
		if( count < len2 )
		    count = len2;
	    }
	    /* a little bit complicated because we need a ulong for count */
	    while( count > len2 ) { /* maybe iterated+salted */
		md_write( md, s2k->salt, 8 );
		md_write( md, pw, pwlen );
		count -= len2;
	    }
	    if( count < 8 )
		md_write( md, s2k->salt, count );
	    else {
		md_write( md, s2k->salt, 8 );
		count -= 8;
                md_write( md, pw, count );
	    }
	}
	else
	    md_write( md, pw, pwlen );
	md_final( md );
	i = md_digest_length( s2k->hash_algo );
	if( i > dek->keylen - used )
	    i = dek->keylen - used;
	memcpy( dek->key+used, md_read(md, s2k->hash_algo), i );
	used += i;
    }
    md_close(md);
}



