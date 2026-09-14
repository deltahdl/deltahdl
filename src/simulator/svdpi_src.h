/* Annex H.14.3: the source-level compatibility include file svdpi_src.h of
 * the deprecated SV3.1a functionality (§H.14). Only two symbols are defined,
 * the macros that let an application declare variables representing the
 * SystemVerilog packed arrays of type bit or logic. Their definitions are
 * implementation-specific, so an application including this file is compiled
 * for the simulator it runs on and recompiled for each other one; an
 * application that does not need it is binary compatible, its DPI C code
 * running on different simulators without recompilation. Neither macro
 * defines an array type (ISO/IEC 9899:1999 6.2.5): each declares a struct
 * holding the chunks of the simulator's representation, which is the
 * canonical one of svdpi_sv31a.h, so that the address of the variable is the
 * svBitPackedArrRef or svLogicPackedArrRef the SV3.1a functions take. */
#ifndef INCLUDED_SVDPI_SRC
#define INCLUDED_SVDPI_SRC

#include "simulator/svdpi_sv31a.h"

#define SV_BIT_PACKED_ARRAY(WIDTH, NAME)         \
  struct {                                       \
    svBitVec32 chunks[SV_CANONICAL_SIZE(WIDTH)]; \
  } NAME

#define SV_LOGIC_PACKED_ARRAY(WIDTH, NAME)         \
  struct {                                         \
    svLogicVec32 chunks[SV_CANONICAL_SIZE(WIDTH)]; \
  } NAME

#endif /* INCLUDED_SVDPI_SRC */
