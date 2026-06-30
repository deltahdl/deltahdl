#include "parser/parser_dpi_validate.h"

#include <format>

#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast.h"

namespace delta {

static bool IsPermittedDpiFormalType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kTime:
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kChandle:
    case DataTypeKind::kNamed:
    case DataTypeKind::kEnum:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      return true;
    default:
      return false;
  }
}

// §35.5.5: the result type of an imported function is restricted to "small
// values" -- a tighter set than the §35.5.6 formal-argument types. The
// permitted results are void, the C-compatible scalar integer and real types,
// chandle, string, and *scalar* (single-bit, unpacked) bit/logic. Packed
// bit/logic vectors, the wide 4-state vector types (integer, time), and
// aggregates (struct/union/enum) are not small values and are rejected here.
// Named/typedef results are accepted and deferred to elaboration, since the
// underlying type is not resolved during parsing. The implicit (omitted) kind
// is handled separately, since §35.5.5 also requires the result type to be
// stated explicitly.
static bool IsPermittedDpiResultType(const DataType& type) {
  switch (type.kind) {
    case DataTypeKind::kVoid:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kChandle:
    case DataTypeKind::kString:
    case DataTypeKind::kNamed:
      return true;
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      // Only the scalar form qualifies; any packed dimension makes it a vector.
      return type.packed_dim_left == nullptr && type.extra_packed_dims.empty();
    default:
      return false;
  }
}

void ValidateDpiResultType(DiagEngine& diag, const ModuleItem* item) {
  if (item->return_type.kind == DataTypeKind::kImplicit) {
    // §35.5.5: an imported function declaration shall explicitly specify a data
    // type or void for its result. Unlike a native function declaration, an
    // omitted (implicit) return type is not allowed.
    diag.Error(item->loc,
               "an imported function must explicitly specify a data type or "
               "void for its result");
  } else if (!IsPermittedDpiResultType(item->return_type)) {
    // §35.5.5: function results are restricted to small values; the type is
    // outside the permitted set.
    diag.Error(item->loc,
               "result type is not permitted for a DPI imported function; "
               "function results are restricted to small values");
  }
}

void ValidateDpiImportNoRefArgs(DiagEngine& diag, const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error(item->loc,
                 "ref qualifier cannot be used in a DPI import declaration");
      break;
    }
  }
}

void ValidateDpiImportFormalTypes(DiagEngine& diag, const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    if (!IsPermittedDpiFormalType(arg.data_type.kind)) {
      diag.Error(item->loc,
                 std::format("type of formal argument '{}' is not permitted "
                             "for a DPI imported subroutine",
                             arg.name));
    } else if (arg.data_type.kind == DataTypeKind::kUnion &&
               !arg.data_type.is_packed) {
      // §35.5.6: among the type-constructing forms in the permitted set, a
      // union is allowed in its packed form only. An unpacked union is
      // therefore not a permitted formal-argument type.
      diag.Error(item->loc,
                 std::format("unpacked union formal argument '{}' is not "
                             "permitted for a DPI imported subroutine; only "
                             "the packed form of a union is allowed",
                             arg.name));
    }
  }
}

}  // namespace delta
