#pragma once

#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct Expr;
struct ModuleItem;

// A type specialized, with the unpacked dimensions it carries: a typedef's own,
// `T t_array [SIZE-1:0]`, or a member's.
struct SpecializedClassType {
  DataType type;
  std::vector<Expr*> unpacked_dims;
};

// §6.25 with §8.25: the type `dtype` names when it reaches a typedef of a
// parameterized class through a specialization, `C#(t_t0,3)::t_array`, or
// through a typedef of one, `MyBaseT::S` under `typedef Base#(32) MyBaseT;`:
// the typedef's type with each type parameter replaced by its actual, each
// packed and unpacked dimension folded with the specialization's values, and
// each member of a structure or union specialized alike. A parameter the
// specialization leaves out takes its default. `module_scope` and `typedefs`
// are the scope the specialization's arguments are written in. Nothing where
// `dtype` names no such typedef, or a class, typedef or dimension this cannot
// resolve.
std::optional<SpecializedClassType> SpecializeClassScopedType(
    const DataType& dtype, const CompilationUnit* unit,
    const ScopeMap& module_scope, const TypedefMap& typedefs, Arena& arena);

// §6.25 (printed pages 144 and 145) with §8.25: a variable declared with a
// typedef a parameterized class declares, reached through a specialization,
// `C#(t_t0,3)::t_array a0;`, takes the type SpecializeClassScopedType gives;
// the typedef's unpacked dimensions become the declaration's, where it writes
// none of its own. Answers whether the declaration was rewritten; one this
// cannot resolve is left as it was.
bool SpecializeClassScopedTypedef(ModuleItem* item, const CompilationUnit* unit,
                                  const ScopeMap& module_scope,
                                  const TypedefMap& typedefs, Arena& arena);

}  // namespace delta
