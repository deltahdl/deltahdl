#pragma once

#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleItem;

// A type specialized, with the unpacked dimensions it carries: a typedef's own,
// `T t_array [SIZE-1:0]`, or a member's. `names_argument` says the type is the
// one an argument of the specialization gives a type parameter, written where
// the specialization is rather than in the class.
struct SpecializedClassType {
  DataType type;
  std::vector<Expr*> unpacked_dims;
  bool names_argument = false;
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

// §8.23 and §8.25 with §16.8: each formal of the sequence or property
// declaration `item` written with a type a class declares, C::t or C#(8)::t,
// rewritten to the type the typedef stands for, under the specialization
// where the class has parameters, the unpacked dimensions the typedef writes
// going to the formal's entry of ModuleItem::prop_formal_unpacked_dims
// (§7.4.4); a formal of a package's type is left as written (§26.3).
void ResolveClassScopedFormalTypes(ModuleItem& item,
                                   const CompilationUnit* unit,
                                   const ScopeMap& module_scope,
                                   const TypedefMap& typedefs, Arena& arena);

// A specialization of a class (§8.25): the class and the arguments it is
// written with, none for the class's unadorned name, which is its default
// specialization.
struct ClassSpecialization {
  const ClassDecl* cls = nullptr;
  const std::vector<DataType>* args = nullptr;
};

// §6.22.1 with §8.25: whether `a` and `b` are one type: specializations of one
// class in which each value parameter takes the same value and each type
// parameter a matching type, a parameter left out taking its default. The
// arguments are written in a scope of the values `module_scope` and the
// typedefs `typedefs`. Nothing where either does not bind.
std::optional<bool> SameSpecialization(const ClassSpecialization& a,
                                       const ClassSpecialization& b,
                                       const ScopeMap& module_scope,
                                       const TypedefMap& typedefs);

// §8.5 and §8.6 with §8.25: `written`, the type a member of `handle`'s class
// declares and the unpacked dimensions it writes, as a handle of that
// specialization reads it: a typedef of the class followed, each type
// parameter replaced by its actual, and each dimension folded with the
// specialization's values. Nothing where the specialization does not bind or
// the type does not specialize.
std::optional<SpecializedClassType> SpecializedMemberType(
    const ClassSpecialization& handle, const SpecializedClassType& written,
    const ScopeMap& module_scope, const TypedefMap& typedefs, Arena& arena);

}  // namespace delta
