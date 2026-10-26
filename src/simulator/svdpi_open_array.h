#pragma once

// Annex H.10.1 has svdpi.h be the one include file of the DPI C layer, fully
// defined by the standard, independent of any implementation or platform and
// the same for every simulator; so what this simulator adds behind an
// svOpenArrayHandle -- the representation the handle points to, which §H.12
// leaves to the implementation -- is declared here, beside the standard's
// file rather than in it. The array functions of svdpi.cpp read it; a test
// that builds an open array to hand the interface includes this header.

#include <stddef.h>

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
//
// ranges holds n_dims entries, the packed part at index 0 and the unpacked
// dimensions after it. has_packed_part is nonzero where the element has a
// packed dimension -- a bit or logic vector, an integer type of predefined
// width, or a packed struct, union or enumeration -- and zero for one with
// none, such as an unpacked struct or a real. 20.7 counts no packed dimension
// for the latter, so the entry at index 0 then stands for nothing.
typedef struct SvOpenArrayDesc {
  void* data;
  int n_dims;
  const SvOpenArrayDimRange* ranges;
  size_t elem_size;
  int has_packed_part;
} SvOpenArrayDesc;

#ifdef __cplusplus
}
#endif
