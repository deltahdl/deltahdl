#include "elaboration/type_eval.h"

#include "elaboration/const_eval.h"
#include "parser/ast.h"

namespace delta {

uint32_t EvalTypeWidth(const DataType& dtype) {
  // If explicit packed dimensions are present, compute from range.
  if (dtype.packed_dim_left && dtype.packed_dim_right) {
    auto left = ConstEvalInt(dtype.packed_dim_left);
    auto right = ConstEvalInt(dtype.packed_dim_right);
    if (left && right) {
      int64_t hi = *left;
      int64_t lo = *right;
      int64_t w = (hi >= lo) ? (hi - lo + 1) : (lo - hi + 1);
      return static_cast<uint32_t>(w);
    }
  }

  // Built-in type widths per IEEE 1800-2023.
  switch (dtype.kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
      return 1;
    case DataTypeKind::kByte:
      return 8;
    case DataTypeKind::kShortint:
      return 16;
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
    case DataTypeKind::kShortreal:
      return 32;
    case DataTypeKind::kLongint:
    case DataTypeKind::kReal:
    case DataTypeKind::kTime:
    case DataTypeKind::kRealtime:
      return 64;
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kNamed:
      return 0;
  }
  return 1;
}

bool Is4stateType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kInteger:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

}  // namespace delta
