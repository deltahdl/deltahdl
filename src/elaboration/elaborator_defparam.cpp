#include <vector>

#include "common/diagnostic.h"
#include "elaboration/const_eval.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "parser/ast.h"

namespace delta {

/// Collect path components from a member-access chain (a.b.c -> [a, b, c]).
static void CollectPathComponents(const Expr* expr,
                                  std::vector<std::string_view>& out) {
  if (expr->kind == ExprKind::kMemberAccess) {
    CollectPathComponents(expr->lhs, out);
    out.push_back(expr->rhs->text);
    return;
  }
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back(expr->text);
  }
}

RtlirParamDecl* Elaborator::ResolveDefparamPath(RtlirModule* root,
                                                const Expr* path_expr) {
  std::vector<std::string_view> parts;
  CollectPathComponents(path_expr, parts);
  if (parts.size() < 2) return nullptr;

  // Walk hierarchy: parts[0..n-2] are instance names, parts[n-1] is param.
  RtlirModule* cur = root;
  for (size_t i = 0; i + 1 < parts.size(); ++i) {
    bool found = false;
    for (auto& child : cur->children) {
      if (child.inst_name == parts[i] && child.resolved) {
        cur = child.resolved;
        found = true;
        break;
      }
    }
    if (!found) return nullptr;
  }

  auto param_name = parts.back();
  for (auto& p : cur->params) {
    if (p.name == param_name) return &p;
  }
  return nullptr;
}

void Elaborator::ApplyDefparams(RtlirModule* top, const ModuleDecl* decl) {
  ScopeMap scope = BuildParamScope(top);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& [path_expr, val_expr] : item->defparam_assigns) {
      auto* param = ResolveDefparamPath(top, path_expr);
      if (!param) {
        diag_.Warning(item->loc, "defparam target not found");
        continue;
      }
      if (param->from_override) continue;  // Instance #(...) takes priority.
      auto val = ConstEvalInt(val_expr, scope);
      if (!val) {
        diag_.Warning(item->loc, "defparam value is not constant");
        continue;
      }
      param->resolved_value = *val;
      param->is_resolved = true;
    }
  }
}

}  // namespace delta
