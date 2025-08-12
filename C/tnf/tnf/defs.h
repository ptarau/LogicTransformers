#ifndef defs_h
#define defs_h

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define XCODE

#ifdef XCODE
static char* fname="/Users/tarau/sit/LogicTransformers/out/tnf_asm.txt";
#else
static char* fname="../../../out/tnf_asm.txt";
#endif

#define TR (1)

#define DEB (1)

// #define GC_ON




#ifdef GC_ON /* ----------------------- WITH GC ENABLED ------------ */
#include "/usr/local/include/gc/gc.h"

#define XALLOC(NbOfEls,TypeOfEls) ((TypeOfEls *)GC_malloc((NbOfEls)*sizeof(TypeOfEls)))

#define XFREE(Ptr)

//#define RALLOC(OldStack,NbOfEls,TypeOfEls) ((TypeOfEls *)GC_realloc(OldStack,(NbOfEls)*sizeof(TypeOfEls)))



#else /**************************  NO BOEHM GC USED ************************************/

#define XALLOC(NbOfEls,TypeOfEls) ((TypeOfEls *)malloc((NbOfEls)*sizeof(TypeOfEls)))

#define XFREE(Ptr) free(Ptr)

//#define RALLOC(OldStack,NbOfEls,TypeOfEls) ((TypeOfEls *)realloc(OldStack,(NbOfEls)*sizeof(TypeOfEls)))

#endif /* GC_ON*/


typedef void *Any;

#endif /* defs_h */
