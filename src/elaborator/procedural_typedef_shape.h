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

// The tables a procedure's declarations are looked up in, and the scope the
// arguments of a specialization written in them fold in.
struct ProceduralTypeScope {
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>>& td_dims;
  const CompilationUnit* unit;
  const ScopeMap& module_scope;
  Arena& arena;
};

// §7.4.4: the type and unpacked dimensions a subroutine's formal, its return
// type or a procedural variable written with the named type `type` takes from
// the array typedef the name stands for, nothing where it stands for none.
//
// §3.12.1 and §26.3: a name written behind a scope, `$unit::arr_t` or
// `p::arr_t`, is that scope's typedef whatever the module declares under the
// bare name, so it is looked up under the key the scope's typedef is recorded
// by; looked up by the bare name, it took the dimensions of the module's own
// arr_t. §8.23: that key is every prefix written before the name,
// `Outer::Inner::t`, as RegisterClassTypedefKeys records a nested class's
// typedef; keyed by the last prefix alone, the name reached the typedef of
// whatever class `Inner` names by itself.
//
// §8.25.1: a name behind a class with parameters, `C#(4)::t`, stands for that
// specialization's typedef, its dimensions folded with the specialization's
// values as a module's variable's are (SpecializeClassScopedType); looked up
// under `C::t`, it took the generic `[p]` whatever the specialization.
std::optional<SpecializedClassType> ArrayTypedefShape(
    const DataType& type, const ProceduralTypeScope& scope);

}  // namespace delta
