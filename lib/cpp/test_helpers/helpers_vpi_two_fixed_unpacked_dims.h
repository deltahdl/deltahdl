#pragma once

#include <vector>

#include "simulator/vpi.h"

using namespace delta;

// One dimension's bounds and extent, as a caller states them. The three travel
// together because VpiArrayDimension holds them together, and naming them once
// keeps MakeTwoFixedUnpackedDims below the five parameters
// readability-function-size.ParameterThreshold allows: stating two dimensions
// positionally took six.
struct FixedUnpackedDim {
  VpiObject* left = nullptr;
  VpiObject* right = nullptr;
  int size = 0;
};

// Builds a two-dimensional fixed-unpacked array-dimension descriptor list whose
// leftmost and rightmost bounds point at the four caller-owned VpiObjects, with
// the given per-dimension sizes. Used by §37.11 instance-array and §37.25
// typespec range-iteration tests to set up a 2-D fixed unpacked shape.
inline std::vector<VpiArrayDimension> MakeTwoFixedUnpackedDims(
    const FixedUnpackedDim& outer, const FixedUnpackedDim& inner) {
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = outer.left;
  dims[0].right_expr = outer.right;
  dims[0].size = outer.size;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = inner.left;
  dims[1].right_expr = inner.right;
  dims[1].size = inner.size;
  return dims;
}
