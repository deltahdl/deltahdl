#include <algorithm>
#include <format>
#include <optional>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

static bool IsTypeParamOf(const ModuleDecl& decl, std::string_view name) {
  if (decl.type_param_names.count(name) != 0) return true;
  return std::ranges::any_of(decl.items, [name](const ModuleItem* item) {
    return item->kind == ModuleItemKind::kParamDecl && item->name == name &&
           item->data_type.kind == DataTypeKind::kVoid;
  });
}

bool Elaborator::NamesADataType(const Expr* value,
                                const RtlirModule* mod) const {
  if (value->kind == ExprKind::kTypeRef) return true;
  if (value->kind != ExprKind::kIdentifier) return false;
  return typedefs_.contains(value->text) ||
         class_names_.contains(value->text) ||
         (mod->decl != nullptr && IsTypeParamOf(*mod->decl, value->text));
}

bool Elaborator::ScopedReadIsParameter(const Expr* access) const {
  if (access->lhs == nullptr || access->rhs == nullptr ||
      access->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const std::string_view kScope = access->lhs->text;
  const std::string_view kName = access->rhs->text;
  for (const PackageDecl* pkg : unit_->packages) {
    if (pkg->name != kScope) continue;
    return std::ranges::any_of(pkg->items, [kName](const ModuleItem* item) {
      return item->kind == ModuleItemKind::kParamDecl && item->name == kName;
    });
  }
  const ClassDecl* cls = FindClassDecl(kScope, unit_);
  return cls != nullptr && ClassParamNames(cls).count(kName) != 0;
}

void Elaborator::AddScopedParameterReads(const Expr* e,
                                         ScopeMap& constants) const {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution &&
      ScopedReadIsParameter(e)) {
    if (std::optional<std::string> key = ScopedNameKey(e))
      constants.try_emplace(*arena_.Create<std::string>(*key), 0);
  }
  ForEachExprChild(
      e, [&](const Expr* child) { AddScopedParameterReads(child, constants); });
}

void Elaborator::ReportOverrideOperands(const ParamList& child_params,
                                        const ModuleDecl& child_decl,
                                        const RtlirModule* mod,
                                        const ScopeMap& parent_scope) {
  for (const ParamOverride& ovr : child_params) {
    const Expr* value = ovr.value_expr;
    if (value == nullptr || IsTypeParamOf(child_decl, ovr.name)) continue;
    if (NamesADataType(value, mod)) {
      diag_.Error(value->range.start,
                  std::format("override of value parameter '{}' of '{}' is a "
                              "data type, not an expression",
                              ovr.name, child_decl.name),
                  Subclause("6.20.2"));
      continue;
    }
    ScopeMap constants = parent_scope;
    AddScopedParameterReads(value, constants);
    if (IsConstantExpr(value, constants) &&
        !CallsNonConstantFunction(value, constants)) {
      continue;
    }
    diag_.Error(value->range.start,
                std::format("override of parameter '{}' of '{}' is not a "
                            "constant expression",
                            ovr.name, child_decl.name),
                Subclause("6.20.2"));
  }
}

}  // namespace delta
