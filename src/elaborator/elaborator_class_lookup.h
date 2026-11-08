#pragma once

#include <string_view>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                     std::string_view name,
                                     const CompilationUnit* unit);

struct OwnedMember {
  const ClassMember* member = nullptr;
  const ClassDecl* owner = nullptr;
};
OwnedMember FindMemberAndOwner(const ClassDecl* cls, std::string_view name,
                               const CompilationUnit* unit);

const ClassDecl* FindClassInPackage(std::string_view pkg_name,
                                    std::string_view cls_name,
                                    const CompilationUnit* unit);

const ClassDecl* FindReferencedClass(const InterfaceRef& ref,
                                     const CompilationUnit* unit);

const ClassDecl* FindNestedClass(const ClassDecl* cls, std::string_view name);

std::vector<const ClassDecl*> ClassChainOfScopePrefix(
    const Expr* prefix, const CompilationUnit* unit);

const ClassDecl* ClassOfDeclaredType(const DataType& dt,
                                     const std::vector<const ClassDecl*>& chain,
                                     const CompilationUnit* unit);

const ClassDecl* ClassOfChainedScope(const DataType& dt,
                                     const CompilationUnit* unit);

}  // namespace delta
