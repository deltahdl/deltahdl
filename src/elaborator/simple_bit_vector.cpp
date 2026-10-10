#include "elaborator/simple_bit_vector.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_type.h"

namespace delta {

static size_t PackedDimCount(const DataType& type) {
  return (type.packed_dim_left != nullptr ? 1 : 0) +
         type.extra_packed_dims.size();
}

bool IsSimpleBitVectorType(const DataType& dtype,
                           const TypeShapeTables& tables) {
  std::vector<std::string_view> names;
  const DataType* type = FollowTypedefs(dtype, tables.typedefs, names);
  if (type == nullptr) return tables.class_names.count(names.back()) == 0;
  size_t dims = PackedDimCount(dtype);
  for (std::string_view name : names) {
    if (tables.typedef_dims.count(name) != 0) return false;
    dims += PackedDimCount(tables.typedefs.at(name));
  }
  switch (type->kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
      return dims <= 1;
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return dims == 0;
    default:
      return false;
  }
}

void ValidateUnboundedParamType(std::string_view name, const DataType* dtype,
                                bool has_unpacked_dims,
                                const TypeShapeTables& tables, DiagEngine& diag,
                                SourceLoc loc) {
  if (!has_unpacked_dims &&
      (dtype == nullptr || IsSimpleBitVectorType(*dtype, tables))) {
    return;
  }
  diag.Error(loc,
             std::format("'$' may be assigned only to a parameter of a simple "
                         "bit vector type, and parameter '{}' is not one",
                         name),
             Subclause("6.20.7"));
}

}  // namespace delta
