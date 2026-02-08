#include "elaboration/type_eval.h"

#include "elaboration/const_eval.h"
#include "parser/ast.h"

namespace delta {

uint32_t eval_type_width(const DataType& dtype) {
  // If explicit packed dimensions are present, compute from range.
  if (dtype.packed_dim_left && dtype.packed_dim_right) {
    auto left = const_eval_int(dtype.packed_dim_left);
    auto right = const_eval_int(dtype.packed_dim_right);
    if (left && right) {
      int64_t hi = *left;
      int64_t lo = *right;
      int64_t w = (hi >= lo) ? (hi - lo + 1) : (lo - hi + 1);
      return static_cast<uint32_t>(w);
    }
  }

  // Built-in type widths per IEEE 1800-2023.
  switch (dtype.kind) {
    case DataTypeKind::Implicit:
      return 1;
    case DataTypeKind::Logic:
      return 1;
    case DataTypeKind::Reg:
      return 1;
    case DataTypeKind::Bit:
      return 1;
    case DataTypeKind::Byte:
      return 8;
    case DataTypeKind::Shortint:
      return 16;
    case DataTypeKind::Int:
      return 32;
    case DataTypeKind::Longint:
      return 64;
    case DataTypeKind::Integer:
      return 32;
    case DataTypeKind::Real:
      return 64;
    case DataTypeKind::Shortreal:
      return 32;
    case DataTypeKind::Time:
      return 64;
    case DataTypeKind::Realtime:
      return 64;
    case DataTypeKind::String:
      return 0;
    case DataTypeKind::Void:
      return 0;
    case DataTypeKind::Named:
      return 0;
  }
  return 1;
}

bool is_4state_type(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::Logic:
    case DataTypeKind::Reg:
    case DataTypeKind::Integer:
    case DataTypeKind::Implicit:
      return true;
    default:
      return false;
  }
}

}  // namespace delta
