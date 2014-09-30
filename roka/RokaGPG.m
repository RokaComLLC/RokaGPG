//
//  RokaGPG.c
//  GPGTestApp
//
//  Created by Mike on 8/28/14.
//  Copyright (c) 2014 RokaCom All rights reserved.
//

#include <stdio.h>
#include "memory.h"
#include "options.h"
#include "RokaGPG.h"
#include "util.h"
#include "main.h"
#include "config.h"
#include "trustdb.h"

@implementation RokaGPG

//
//Return a list of users that BEGIN with the matchingString
//
+ (NSMutableArray *) getUsers:(NSString *) matchingString{
    NSMutableArray *users = [[NSMutableArray alloc] init];;
    
    
   // users[0]=@"bob*";
    
    //users[0] = @"bob@rokacom.com";
    //users[1] = @"bob@aol.com";
    //users[2] = @"bob@bobnet.com";
    

    
    /* We need to do the stale check right here because it might need to
     update the keyring while we already have the keyring open.  This
     is very bad for W32 because of a sharing violation. For real OSes
     it might lead to false results if we are later listing a keyring
     which is associated with the inode of a deleted file.  */
    check_trustdb_stale ();
    
    
    //get_all_userids( 0 );
    
    KEYDB_HANDLE hd;
    KBNODE keyblock = NULL;
    int rc=0;
    
    hd = keydb_new (0);
    if (!hd)
        rc = G10ERR_GENERAL;
    else
        rc = keydb_search_first (hd);
    if( rc ) {
        if( rc != -1 )
            log_error("keydb_search_first failed: %s\n", g10_errstr(rc) );
        goto leave;
    }
    
    do {
        rc = keydb_get_keyblock (hd, &keyblock);
        if (rc) {
            log_error ("keydb_get_keyblock failed: %s\n", g10_errstr(rc));
            goto leave;
        }
        
        merge_keys_and_selfsig( keyblock );
        
        do_reorder_keyblock(keyblock,1);
        do_reorder_keyblock(keyblock,0);
        
        KBNODE kbctx;
        KBNODE node;
        
        /* get the keyid from the keyblock */
        node = find_kbnode( keyblock, PKT_PUBLIC_KEY );
        if( !node ) {
            goto leave;
        }
        
        
        for( kbctx=NULL; (node=walk_kbnode( keyblock, &kbctx, 0)) ; ) {
            if( node->pkt->pkttype == PKT_USER_ID && !opt.fast_list_mode ) {
                PKT_user_id *uid=node->pkt->pkt.user_id;

                NSString *tmpUID = [NSString stringWithUTF8String:uid->name];
                NSLog(@"tmpUID: %@",tmpUID);
                if( [tmpUID hasPrefix:matchingString]){
                    [users addObject:tmpUID];
                }
                
                
            }
            
        }
        putchar('\n');
        
        release_kbnode( keyblock );
        keyblock = NULL;
    } while (!(rc = keydb_search_next (hd)));
    
leave:
    release_kbnode (keyblock);
    keydb_release (hd);
    
    
    NSLog(@"users %@",users);
    
    return users;
}

+ (NSString *)pathForTemporaryFileWithPrefix:(NSString *)prefix
{
    NSString *  result;
    CFUUIDRef   uuid;
    CFStringRef uuidStr;
    
    uuid = CFUUIDCreate(NULL);
    assert(uuid != NULL);
    
    uuidStr = CFUUIDCreateString(NULL, uuid);
    assert(uuidStr != NULL);
    
    result = [NSTemporaryDirectory() stringByAppendingPathComponent:[NSString stringWithFormat:@"%@-%@", prefix, uuidStr]];
    assert(result != nil);
    
    CFRelease(uuidStr);
    CFRelease(uuid);
    
    return result;
}




+ (BOOL) importPublicKeyFromFileAtPath:(NSString *)path{
    BOOL bRetVal = FALSE;
    
    char *paths[2];
    paths[0] = [path UTF8String];
    paths[1] = NULL;
    
    import_keys(paths,1,NULL,opt.import_options);
    
    
    return bRetVal;
}


+ (NSString *) getPubKeyFromKeyRing:(STRLIST)userID
{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSError *error;
    NSString *RetVal = nil;
    
    //Create Temporary file
    NSString *outFileName = [self pathForTemporaryFileWithPrefix:@"pubkey"];
    

    //Set the outfile
    //NSString *outFileName = [self pathForTemporaryFileWithPrefix:@"out"];
    //opt.outfile =  [outFileName UTF8String];
    
    opt.outfile = [outFileName UTF8String];
    
    //export the keys
    export_pubkeys( NULL,opt.export_options );
    
    
    //Read contents and convert to NSString
    RetVal = [[NSString alloc] initWithContentsOfFile:outFileName
                                         usedEncoding:nil
                                                error:nil];
    
    //Delete Temporary Files
    [fileManager removeItemAtPath:outFileName error:&error];
    
    opt.outfile = NULL;
    
    return RetVal;
}



+ (NSString *) decryptStr:(NSString *)cipherText
{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSError *error;
    NSString *RetVal = nil;
    
    //Create Temporary file
    NSString *tmpFile = [self pathForTemporaryFileWithPrefix:@"ctxt"];
    
    //NSLog(@"tmpFile: %@",tmpFile);
    
    //Write String to it
    [cipherText writeToFile:tmpFile atomically:NO encoding:NSStringEncodingConversionAllowLossy error:nil];
    
    //Set the outfile
    NSString *outFileName = [self pathForTemporaryFileWithPrefix:@"out"];
    opt.outfile =  [outFileName UTF8String];
    
    //Encrypt file
    decrypt_message( [tmpFile UTF8String]);
    
    
    //Read contents and convert to NSString
    RetVal = [[NSString alloc] initWithContentsOfFile:outFileName
                                         usedEncoding:nil
                                                error:nil];
    
    //Delete Temporary Files
    [fileManager removeItemAtPath:tmpFile error:&error];
    [fileManager removeItemAtPath:outFileName error:&error];
    
    opt.outfile = NULL;
    
    return RetVal;
}


#ifdef LEGACY
+ (NSString *) encryptStr:(char *)inStr toUsers:(STRLIST)users
{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSError *error;
    
    NSString *plainText = [NSString stringWithUTF8String:inStr];
    
    //Create Temporary file
    NSString *tmpFile = [self pathForTemporaryFileWithPrefix:@"key"];
    
    NSLog(@"tmpFile: %@",tmpFile);
    
    //Write String to it
    [plainText writeToFile:tmpFile atomically:NO encoding:NSStringEncodingConversionAllowLossy error:nil];
    
    //Set the outfile
    NSString *outFileName = [tmpFile stringByAppendingString:@".asc"];
    
    //Encrypt file
    encode_crypt( [tmpFile UTF8String], users,0 );
    
    NSLog(@"outFile: %@",outFileName);
    
    //Read contents and convert to NSString
    NSString *RetVal = [[NSString alloc] initWithContentsOfFile:outFileName
                                                   usedEncoding:nil
                                                          error:nil];
    
    //Delete Temporary Files
    [fileManager removeItemAtPath:tmpFile error:&error];
    [fileManager removeItemAtPath:outFileName error:&error];
    
    
    return RetVal;
}
#endif



//Encrypt the string to a single user
+ (NSString *) encryptStr:(NSString *)plainText toUser:(NSString *)user
{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSError *error;

    
    //Convert User to STRLIST
    STRLIST sl = NULL;
    add_to_strlist(&sl,[user UTF8String]);
    
    //Create Temporary file, with the text verision of the plaintext
    NSString *tmpFile = [self pathForTemporaryFileWithPrefix:@"key"];
    
    NSLog(@"tmpFile: %@",tmpFile);
    
    //Write String to it
    [plainText writeToFile:tmpFile atomically:NO encoding:NSStringEncodingConversionAllowLossy error:nil];
    
    //Set the outfile
    NSString *outFileName = [tmpFile stringByAppendingString:@".asc"];

    //Encrypt file
    encode_crypt( [tmpFile UTF8String], sl,0 );
    
    NSLog(@"outFile: %@",outFileName);
    
    //Read contents and convert to NSString
    NSString *RetVal = [[NSString alloc] initWithContentsOfFile:outFileName
                                usedEncoding:nil
                                       error:nil];

    //Delete Temporary Files
    [fileManager removeItemAtPath:tmpFile error:&error];
    [fileManager removeItemAtPath:outFileName error:&error];
    
    
    return RetVal;
}

//Encrypt a string to the list of user's provided by the Array
+ (NSString *) encryptStr:(NSString *)plainText toUsers:(NSArray *)users
{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSError *error;
    
    
    //Convert Userlist to STRLIST
    STRLIST sl = NULL;
    
    for (NSString * object in users) {
		//[data addChild:[self valueElementFromObject:object]];
        NSLog(@"User: %@", object);
        add_to_strlist(&sl,[object UTF8String]);
	}
    
    
    //Create Temporary file, with the text verision of the plaintext
    NSString *tmpFile = [self pathForTemporaryFileWithPrefix:@"key"];
    
    NSLog(@"tmpFile: %@",tmpFile);
    
    //Write String to it
    [plainText writeToFile:tmpFile atomically:NO encoding:NSStringEncodingConversionAllowLossy error:nil];
    
    //Set the outfile
    NSString *outFileName = [tmpFile stringByAppendingString:@".asc"];
    
    //Encrypt file
    encode_crypt( [tmpFile UTF8String], sl,0 );
    
    NSLog(@"outFile: %@",outFileName);
    
    //Read contents and convert to NSString
    NSString *RetVal = [[NSString alloc] initWithContentsOfFile:outFileName
                                                   usedEncoding:nil
                                                          error:nil];
    
    //Delete Temporary Files
    [fileManager removeItemAtPath:tmpFile error:&error];
    [fileManager removeItemAtPath:outFileName error:&error];
    
    
    return RetVal;
}



+(void) setPassphrase:(char *)passphrase{
    
    set_next_passphrase( passphrase );
    
}

/* We need the home directory also in some other directories, so make
 sure that both variables are always in sync. */
void
set_homedir (char *dir)
{
    if (!dir)
        dir = "";
    g10_opt_homedir = opt.homedir = dir;
}



//Must be done after set_homedir otherwise bad things happen
void
set_keyrings()
{
    
    
    //From g10/gpg.c
    /* Add the keyrings, but not for some special commands and not in
     case of "-kvv userid keyring".  Also avoid adding the secret
     keyring for a couple of commands to avoid unneeded access in
     case the secrings are stored on a floppy.
     
     We always need to add the keyrings if we are running under
     SELinux, this is so that the rings are added to the list of
     secured files. */
    
    
    // if (!sec_nrings || default_keyring) /* add default secret rings */
    keydb_add_resource ("secring" EXTSEP_S "gpg", 4, 1);
    //for (sl = sec_nrings; sl; sl = sl->next)
    //keydb_add_resource ( sl->d, 0, 1 );
    
    //f( !nrings || default_keyring )  /* add default ring */
    keydb_add_resource ("pubring" EXTSEP_S "gpg", 4, 0);
    //for(sl = nrings; sl; sl = sl->next )
    //  keydb_add_resource ( sl->d, sl->flags, 0 );
    
    //  FREE_STRLIST(nrings);
    //FREE_STRLIST(sec_nrings);
    
    
    
}



void RokaGPG_Init(){
    
    secmem_set_flags( secmem_get_flags() | 2 ); /* suspend warnings */
  
    
    secure_randoxmalloc(); /* put random number into secure memory */
    
    
    //Set the global options
    opt.armor = 1;
    opt.command_fd = -1; /* no command fd */
    opt.compress_level = -1; /* defaults to standard compress level */
    opt.bz2_compress_level = -1; /* defaults to standard compress level */
    /* note: if you change these lines, look at oOpenPGP */
    opt.def_cipher_algo = CIPHER_ALGO_AES256;
    opt.def_digest_algo = 0;
    opt.cert_digest_algo = 0;
    opt.compress_algo = -1; /* defaults to DEFAULT_COMPRESS_ALGO */
    opt.s2k_mode = 3; /* iterated+salted */
    opt.s2k_count = 96; /* 65536 iterations */

    //opt.s2k_cipher_algo = CIPHER_ALGO_CAST5;
   // opt.s2k_cipher_algo = CIPHER_ALGO_3DES;
    opt.s2k_cipher_algo = CIPHER_ALGO_AES256;
    opt.completes_needed = 1;
    opt.marginals_needed = 3;
    opt.max_cert_depth = 5;
    opt.pgp2_workarounds = 1;
    opt.escape_from = 1;
    opt.flags.require_cross_cert = 1;
    opt.import_options=IMPORT_SK2PK;
    opt.export_options=EXPORT_ATTRIBUTES;
    opt.trust_model = TM_ALWAYS;
    opt.textmode = 1;
    
   // secmem_init(32768);  //Value from g10/gpg.c
    
    secmem_init(4194304);
    
    //Set up the trustDB
     setup_trustdb(1, "trustdb.gpg");
    

}


void list_private_keys(const char *userID){
    
    
    STRLIST sl = NULL;

    add_to_strlist2( &sl, userID, 0 );
    secret_key_list( sl );
    free_strlist(sl);
}


void
g10_exit( int rc )
{

    update_random_seed_file();
    
    /*
    if( opt.debug & DBG_MEMSTAT_VALUE ) {
        m_print_stats("on exit");
        random_dump_stats();
    }
    if( opt.debug )
        secmem_dump_stats();
    secmem_term();
     */
    exit(rc );
}

@end

