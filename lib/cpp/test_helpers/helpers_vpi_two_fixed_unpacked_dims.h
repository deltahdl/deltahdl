#pragma once

#include <vector>

#include "simulator/vpi.h"

using namespace delta;

// Builds a two-dimensional fixed-unpacked array-dimension descriptor list whose
// leftmost and rightmost bounds point at the four caller-owned VpiObjects, with
// the given per-dimension sizes. Used by §37.11 instance-array and §37.25
// typespec range-iteration tests to set up a 2-D fixed unpacked shape.
inline std::vector<VpiArrayDimension> MakeTwoFixedUnpackedDims(
    VpiObject* l0, VpiObject* r0, int size0, VpiObject* l1, VpiObject* r1,
    int size1) {
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = l0;
  dims[0].right_expr = r0;
  dims[0].size = size0;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = l1;
  dims[1].right_expr = r1;
  dims[1].size = size1;
  return dims;
}
