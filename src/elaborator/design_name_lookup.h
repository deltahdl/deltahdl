#pragma once

#include <string_view>
#include <vector>

#include "parser/ast_class.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;

const ModuleDecl* FindDefinition(const CompilationUnit* unit,
                                 std::string_view name);

const PackageDecl* FindPackage(const CompilationUnit* unit,
                               std::string_view name);

const ModuleDecl* ModuleAlongPath(const CompilationUnit* unit,
                                  const ModuleDecl* decl,
                                  const std::vector<std::string_view>& path);

const ModuleItem* SubroutineAmong(const std::vector<ModuleItem*>& items,
                                  std::string_view name);

const ClassMember* ClassMemberOf(const ClassDecl* cls, std::string_view name,
                                 ClassMemberKind kind,
                                 const CompilationUnit* unit);

const ModuleItem* MethodOf(const ClassDecl* cls, std::string_view name,
                           const CompilationUnit* unit);

}  // namespace delta
