#include "elaborator/elaborator_type_facts.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

static const DataType& ResolvedType(const DataType& dtype,
                                    const TypedefMap& typedefs) {
  const DataType* cur = &dtype;
  for (size_t steps = 0; steps <= typedefs.size(); ++steps) {
    if (cur->kind != DataTypeKind::kNamed) return *cur;
    auto it = typedefs.find(cur->type_name);
    if (it == typedefs.end()) return *cur;
    cur = &it->second;
  }
  return *cur;
}

static std::optional<PackedRange> TypeNameRange(const DataType& dtype,
                                                const TypedefMap& typedefs) {
  if (dtype.kind == DataTypeKind::kNamed && dtype.packed_dim_left != nullptr)
    return std::nullopt;
  const DataType& end = ResolvedType(dtype, typedefs);
  if (end.kind == DataTypeKind::kNamed || end.packed_dim_left == nullptr ||
      end.packed_dim_right == nullptr || !end.extra_packed_dims.empty()) {
    return std::nullopt;
  }
  auto left = ConstEvalInt(end.packed_dim_left);
  auto right = ConstEvalInt(end.packed_dim_right);
  if (!left || !right) return std::nullopt;
  return PackedRange{*left, *right};
}

static uint32_t TypeNameWidth(const DataType& dtype, const TypedefMap& typedefs,
                              bool is_aggregate) {
  if (is_aggregate || dtype.kind == DataTypeKind::kImplicit) return 0;
  return EvalTypeWidth(dtype, typedefs);
}

void PopulateTypeWidths(const TypeNameSources& src, TypeNameFacts& out) {
  for (const auto& [name, dtype] : src.typedefs) {
    out.widths[name] =
        TypeNameWidth(dtype, src.typedefs, src.aggregates.count(name) > 0);
    out.kinds[name] = ResolvedTypeKind(dtype, src.typedefs);
    out.is_signed[name] = IsSignedType(dtype, src.typedefs);
    const DataType& end = ResolvedType(dtype, src.typedefs);
    if (end.kind == DataTypeKind::kNamed && end.type_name != name) {
      out.targets[name] = end.type_name;
    }
    if (end.kind == DataTypeKind::kEnum) {
      out.enums[name] = src.arena.Create<DataType>(end);
    }
    if (end.kind == DataTypeKind::kVirtualInterface) {
      out.interfaces[name] = end.type_name;
    }
    if (auto range = TypeNameRange(dtype, src.typedefs)) {
      out.ranges[name] = *range;
    }
    if (dtype.kind != DataTypeKind::kStruct &&
        dtype.kind != DataTypeKind::kUnion) {
      continue;
    }
    auto* copy = src.arena.Create<DataType>(dtype);
    ResolveNestedAggregateTypes(*copy, src.typedefs, src.arena);
    out.layouts[name] = copy;
  }
}

}  // namespace delta
