#pragma once

#include <vector>

#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

using namespace delta;

struct FixedUnpackedDim {
  VpiObject* left = nullptr;
  VpiObject* right = nullptr;
  int size = 0;
};

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
