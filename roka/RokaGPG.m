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
    
    import_keys([path UTF8String],1,NULL,opt.import_options);
    
    
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



+ (NSString *) decryptStr:(char *)inStr
{
    NSFileManager *fileManager = [NSFileManager defaultManager];
    NSError *error;
    NSString *RetVal = nil;
    
    NSString *cipherText = [NSMutableString stringWithUTF8String:inStr];
    
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
    opt.def_cipher_algo = 0;
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

