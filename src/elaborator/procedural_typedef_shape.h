#pragma once

#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct Expr;

struct ProceduralTypeScope {
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>>& td_dims;
  const CompilationUnit* unit;
  const ScopeMap& module_scope;
  Arena& arena;
};

std::optional<SpecializedClassType> ArrayTypedefShape(
    const DataType& type, const ProceduralTypeScope& scope);

}  // namespace delta
