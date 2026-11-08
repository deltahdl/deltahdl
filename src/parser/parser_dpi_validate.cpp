#include "parser/parser_dpi_validate.h"

#include <format>

#include "common/diagnostic.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

DpiFormalTypeVerdict ClassifyDpiFormalType(const DataType& type) {
  if (!IsPermittedDpiFormalType(type.kind)) {
    return DpiFormalTypeVerdict::kNotPermittedType;
  }
  if (type.kind == DataTypeKind::kUnion && !type.is_packed) {
    return DpiFormalTypeVerdict::kUnpackedUnion;
  }
  for (const StructMember& member : type.struct_members) {
    if (!IsPermittedDpiFormalType(member.type_kind)) {
      return DpiFormalTypeVerdict::kNotPermittedType;
    }
    if (member.nested_type != nullptr) {
      DpiFormalTypeVerdict nested = ClassifyDpiFormalType(*member.nested_type);
      if (nested != DpiFormalTypeVerdict::kPermitted) return nested;
    }
  }
  return DpiFormalTypeVerdict::kPermitted;
}

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
      return type.packed_dim_left == nullptr && type.extra_packed_dims.empty();
    default:
      return false;
  }
}

void ValidateDpiResultType(DiagEngine& diag, const ModuleItem* item) {
  if (item->return_type.kind == DataTypeKind::kImplicit) {
    diag.Error(item->loc,
               "an imported function must explicitly specify a data type or "
               "void for its result",
               Subclause("35.5.5"));
  } else if (!IsPermittedDpiResultType(item->return_type)) {
    diag.Error(item->loc,
               "result type is not permitted for a DPI imported function; "
               "function results are restricted to small values",
               Subclause("35.5.5"));
  }
}

void ValidateDpiImportNoRefArgs(DiagEngine& diag, const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error(item->loc,
                 "ref qualifier cannot be used in a DPI import declaration",
                 Subclause("35.5.4"));
      break;
    }
  }
}

void ValidateDpiImportFormalTypes(DiagEngine& diag, const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    switch (ClassifyDpiFormalType(arg.data_type)) {
      case DpiFormalTypeVerdict::kNotPermittedType:
        diag.Error(item->loc,
                   std::format("type of formal argument '{}' is not permitted "
                               "for a DPI imported subroutine",
                               arg.name),
                   Subclause("35.5.6"));
        break;
      case DpiFormalTypeVerdict::kUnpackedUnion:
        diag.Error(item->loc,
                   std::format("unpacked union formal argument '{}' is not "
                               "permitted for a DPI imported subroutine; only "
                               "the packed form of a union is allowed",
                               arg.name),
                   Subclause("35.5.6"));
        break;
      case DpiFormalTypeVerdict::kPermitted:
        break;
    }
  }
}

void ValidateDpiImportOpenArrayPackedDims(DiagEngine& diag,
                                          const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    const DataType& type = arg.data_type;
    if (!type.has_unsized_packed_dim) continue;
    if (type.packed_dim_left == nullptr && type.extra_packed_dims.empty()) {
      continue;
    }
    diag.Error(item->loc,
               std::format("formal argument '{}' gives a packed dimension no "
                           "range alongside a sized one; a packed dimension "
                           "left unspecified must be the only packed dimension "
                           "of the argument",
                           arg.name),
               Subclause("35.5.6.1"));
  }
}

}  // namespace delta
