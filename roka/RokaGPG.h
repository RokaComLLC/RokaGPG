//
// RokaGPG
//  Created by Mike on 8/28/14.
//  Copyright (c) 2014 Aperture Technology. All rights reserved.
//

#import <Foundation/Foundation.h>

#include "types.h"

@interface RokaGPG : NSObject

void generate_keypair (const char *userID, const char *passPhrase);
void list_private_keys(const char *userID);
void set_homedir (char *dir);
void set_keyrings(void);


void g10_exit( int rc );
void RokaGPG_Init(void);


+ (NSString *) encryptStr:(NSString *)plainText toUser:(NSString *)user;
+ (NSString *) decryptStr:(NSString *)cipherText;

+(void) setPassphrase:(char *)passphrase;

+ (NSString *) getPubKeyFromKeyRing:(STRLIST)userID;

+ (BOOL) importPublicKeyFromFileAtPath:(NSString *)path;


@end