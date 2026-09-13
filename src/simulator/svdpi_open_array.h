#pragma once

// Annex H.10.1 has svdpi.h be the one include file of the DPI C layer, fully
// defined by the standard, independent of any implementation or platform and
// the same for every simulator; so what this simulator adds behind an
// svOpenArrayHandle -- the representation the handle points to, which §H.12
// leaves to the implementation -- is declared here, beside the standard's
// file rather than in it. The array functions of svdpi.cpp read it; a test
// that builds an open array to hand the interface includes this header.

#include <stddef.h>

#include "simulator/svdpi.h"

#ifdef __cplusplus
extern "C" {
#endif

// Backing representation an svOpenArrayHandle points to. The array querying
// functions of Annex H.12.2 are modeled on the SystemVerilog array querying
// functions (20.7), so each dimension is described by its declared left and
// right bounds; low/high/size/increment are then derived exactly as 20.7
// defines them. The dimension at index 0 describes the single packed part of
// the array and the dimensions at indices greater than 0 describe the unpacked
// part, following H.12.2's dimension-numbering convention.
typedef struct SvOpenArrayDimRange {
  int left;
  int right;
} SvOpenArrayDimRange;

// elem_size is the byte stride of one array element within the actual
// representation that data points at. Annex H.12.4's element-address functions
// use it to step between consecutive elements. A value of 0 marks an element
// representation that differs from that of an individual value of the same
// type, for which H.12.4 requires those functions to return a null pointer.
typedef struct SvOpenArrayDesc {
  void* data;
  int n_dims;
  const SvOpenArrayDimRange* ranges;
  size_t elem_size;
} SvOpenArrayDesc;

#ifdef __cplusplus
}
#endif
