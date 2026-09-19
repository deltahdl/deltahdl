/* Annex H.14.2: the svdpi.h definitions for SV3.1a-style packed data
 * processing, deprecated functionality an IEEE Std 1800 simulator need not
 * implement (§H.14) and is not obligated to provide the definitions and
 * prototypes of in its include file (§H.14.1). This simulator provides them
 * beside svdpi.h rather than in it, so that svdpi.h stays the file Annex I
 * shows; an SV3.1a-compatible application includes this file after it.
 *
 * Two things in the deprecated portion Annex I.3 prints are not as this file
 * has them. svBitVec32 is uint32_t here as §H.14.2 spells it, where the
 * portion spells it unsigned int, one type on every platform this file
 * supports. And the portion also declares sixteen functions that copy a
 * packed array between the canonical representation and an element of an
 * open array, svPutBitArrElemVec32 and svGetLogicArrElem3Vec32 among them,
 * which §H.14.2 does not list and this simulator does not provide; §H.14.1
 * leaves an implementation free to provide none of the portion.
 *
 * Under §H.14 a packed data argument of a declaration annotated "DPI" crosses
 * as an opaque handle to the actual vendor representation, which for this
 * simulator is the canonical representation itself: a bit array is an array of
 * 32-bit chunks and a logic array an array of aval/bval pairs, least
 * significant chunk first, indexed n-1:0 with 0 the LSB. The translation
 * functions copy whole arrays between that representation and canonical
 * buffers the user allocates, of a width the user provides, the unused bits
 * undetermined; the bit-select and part-select functions read and write the
 * representation in place, a part-select being a narrow (<= 32 bits) slice of
 * a packed array of bit or logic copied between the implementation
 * representation part [w+i-1:i] and the canonical chunk part [w-1:0],
 * undetermined where the range lies outside the array's normalized range. */
#ifndef INCLUDED_SVDPI_SV31A
#define INCLUDED_SVDPI_SV31A

#include <stdint.h>

#include "simulator/svdpi.h"

#ifdef __cplusplus
extern "C" {
#endif

/* svdpi.h undefines its linkage macros at its end, so the prototypes below
   carry the same linkage spelled again the way that file spells it. */
#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#define SV31A_XXTERN __declspec(dllimport)
#else
#define SV31A_XXTERN
#endif

/* 2-state and 4-state vectors, modeled upon PLI's avalue/bvalue */
#define SV_CANONICAL_SIZE(WIDTH) (((WIDTH) + 31) >> 5)

typedef uint32_t svBitVec32; /* (a chunk of) packed bit array */

typedef struct {
  unsigned int c;
  unsigned int d;
} svLogicVec32; /* (a chunk of) packed logic array */

/* reference to a standalone packed array */
typedef void* svBitPackedArrRef;
typedef void* svLogicPackedArrRef;

/* total size in bytes of the simulator's representation of a packed array */
/* width in bits */
SV31A_XXTERN int svSizeOfBitPackedArr(int width);
SV31A_XXTERN int svSizeOfLogicPackedArr(int width);

/* s=source, d=destination, w=width */
/* actual <-- canonical */
SV31A_XXTERN void svPutBitVec32(svBitPackedArrRef d, const svBitVec32* s,
                                int w);
SV31A_XXTERN void svPutLogicVec32(svLogicPackedArrRef d, const svLogicVec32* s,
                                  int w);

/* canonical <-- actual */
SV31A_XXTERN void svGetBitVec32(svBitVec32* d, svBitPackedArrRef s, int w);
SV31A_XXTERN void svGetLogicVec32(svLogicVec32* d, svLogicPackedArrRef s,
                                  int w);

/* Packed arrays are assumed to be indexed n-1:0, where 0 is the index of
   LSB */
/* functions for bit-select */
/* s=source, i=bit-index */
SV31A_XXTERN svBit svGetSelectBit(svBitPackedArrRef s, int i);
SV31A_XXTERN svLogic svGetSelectLogic(svLogicPackedArrRef s, int i);

/* d=destination, i=bit-index, s=scalar */
SV31A_XXTERN void svPutSelectBit(svBitPackedArrRef d, int i, svBit s);
SV31A_XXTERN void svPutSelectLogic(svLogicPackedArrRef d, int i, svLogic s);

/* functions for part-select: s=source, d=destination, i=starting bit index,
   w=width like for variable part-selects; limitations: w <= 32 */
/* canonical <-- actual */
SV31A_XXTERN void svGetPartSelectBit(svBitVec32* d, svBitPackedArrRef s, int i,
                                     int w);
SV31A_XXTERN svBitVec32 svGetBits(svBitPackedArrRef s, int i, int w);
SV31A_XXTERN svBitVec32 svGet32Bits(svBitPackedArrRef s, int i); /* 32-bits */
SV31A_XXTERN uint64_t svGet64Bits(svBitPackedArrRef s, int i);   /* 64-bits */
SV31A_XXTERN void svGetPartSelectLogic(svLogicVec32* d, svLogicPackedArrRef s,
                                       int i, int w);

/* actual <-- canonical */
SV31A_XXTERN void svPutPartSelectBit(svBitPackedArrRef d, svBitVec32 s, int i,
                                     int w);
SV31A_XXTERN void svPutPartSelectLogic(svLogicPackedArrRef d, svLogicVec32 s,
                                       int i, int w);

#undef SV31A_XXTERN

#ifdef __cplusplus
}
#endif

#endif /* INCLUDED_SVDPI_SV31A */
