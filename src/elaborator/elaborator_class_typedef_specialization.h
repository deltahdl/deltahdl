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

struct SpecializedClassType {
  DataType type;
  std::vector<Expr*> unpacked_dims;
  bool names_argument = false;
};

std::optional<SpecializedClassType> SpecializeClassScopedType(
    const DataType& dtype, const CompilationUnit* unit,
    const ScopeMap& module_scope, const TypedefMap& typedefs, Arena& arena);

bool SpecializeClassScopedTypedef(ModuleItem* item, const CompilationUnit* unit,
                                  const ScopeMap& module_scope,
                                  const TypedefMap& typedefs, Arena& arena);

void ResolveClassScopedFormalTypes(ModuleItem& item,
                                   const CompilationUnit* unit,
                                   const ScopeMap& module_scope,
                                   const TypedefMap& typedefs, Arena& arena);

struct ClassSpecialization {
  const ClassDecl* cls = nullptr;
  const std::vector<DataType>* args = nullptr;
};

std::optional<bool> SameSpecialization(const ClassSpecialization& a,
                                       const ClassSpecialization& b,
                                       const ScopeMap& module_scope,
                                       const TypedefMap& typedefs);

std::optional<SpecializedClassType> SpecializedMemberType(
    const ClassSpecialization& handle, const SpecializedClassType& written,
    const ScopeMap& module_scope, const TypedefMap& typedefs, Arena& arena);

const std::vector<DataType>* SpecializedExtendsArguments(
    const ClassSpecialization& handle, const ScopeMap& module_scope,
    const TypedefMap& typedefs, Arena& arena);

}  // namespace delta
