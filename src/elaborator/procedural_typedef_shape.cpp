#include "elaborator/procedural_typedef_shape.h"

#include <optional>
#include <string>

#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

std::optional<SpecializedClassType> ArrayTypedefShape(
    const DataType& type, const ProceduralTypeScope& scope) {
  auto spec = SpecializeClassScopedType(type, scope.unit, scope.module_scope,
                                        scope.typedefs, scope.arena);
  if (spec.has_value()) {
    if (spec->unpacked_dims.empty()) return std::nullopt;
    return spec;
  }
  const std::string kKey = TypeChainKey(type);
  auto base = scope.typedefs.find(kKey);
  auto dims = scope.td_dims.find(kKey);
  if (base == scope.typedefs.end() || dims == scope.td_dims.end())
    return std::nullopt;
  return SpecializedClassType{base->second, dims->second};
}

}  // namespace delta
