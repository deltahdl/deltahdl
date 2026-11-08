#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir_enum_member.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

using EnumTypeVisitor = std::function<void(std::string_view member_path,
                                           const DataType& enum_type)>;
void ForEachEnumTypeIn(const DataType& type, const EnumTypeVisitor& fn);

void ForEachEnumTypeOfItem(const ModuleItem* item, const EnumTypeVisitor& fn);

bool ExprContainsXZ(const Expr* e);

std::vector<RtlirEnumMember> FoldEnumMembers(
    const std::vector<EnumMember>& decl_members, const ScopeMap& scope,
    Arena& arena);

std::vector<std::string> EnumMemberDeclaredNames(const EnumMember& member,
                                                 const ScopeMap& scope);

std::vector<RtlirEnumMember> BindEnumConstantsOfItem(const ModuleItem* item,
                                                     ScopeMap& scope,
                                                     Arena& arena);

void BindPackageImportConstants(const PackageDecl* pkg, const ModuleItem* imp,
                                const ScopeMap& cu_param_scope,
                                ScopeMap& scope);

}  // namespace delta
