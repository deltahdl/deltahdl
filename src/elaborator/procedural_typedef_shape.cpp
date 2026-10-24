#include "elaborator/procedural_typedef_shape.h"

#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_type.h"

namespace delta {

// The key a named type's typedef is recorded by: every prefix written before
// the name, then NamedTypeKey's last prefix and name. A leading `$unit` is
// left off, the compilation unit's classes' typedefs being recorded by the
// class's own name (RegisterClassTypedefs in elaborator_resolve.cpp).
static std::string TypedefChainKey(const DataType& type) {
  const std::vector<std::string_view>& outer = type.outer_scope_names;
  size_t first = !outer.empty() && outer.front() == "$unit" ? 1 : 0;
  std::string key;
  for (size_t i = first; i < outer.size(); ++i)
    key += std::string(outer[i]) + "::";
  return key + NamedTypeKey(type);
}

std::optional<SpecializedClassType> ArrayTypedefShape(
    const DataType& type, const ProceduralTypeScope& scope) {
  auto spec = SpecializeClassScopedType(type, scope.unit, scope.module_scope,
                                        scope.typedefs, scope.arena);
  if (spec.has_value()) {
    if (spec->unpacked_dims.empty()) return std::nullopt;
    return spec;
  }
  const std::string kKey = TypedefChainKey(type);
  auto base = scope.typedefs.find(kKey);
  auto dims = scope.td_dims.find(kKey);
  if (base == scope.typedefs.end() || dims == scope.td_dims.end())
    return std::nullopt;
  return SpecializedClassType{base->second, dims->second};
}

}  // namespace delta
