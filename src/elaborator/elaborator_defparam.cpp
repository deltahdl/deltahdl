#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
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
                                                const Expr* path_expr,
                                                RtlirModule** out_mod) {
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
    if (p.name == param_name) {
      if (out_mod) *out_mod = cur;
      return &p;
    }
  }
  return nullptr;
}

void Elaborator::RecomputeDependentParams(RtlirModule* mod) {
  if (!mod) return;
  for (auto& p : mod->params) {
    if (p.from_override) continue;
    if (p.is_type_param) continue;
    if (p.is_unbounded) continue;
    if (!p.default_value) continue;
    auto scope = BuildParamScope(mod);
    auto val = ConstEvalInt(p.default_value, scope);
    if (val) {
      p.resolved_value = *val;
      p.is_resolved = true;
    }
  }
}

void Elaborator::ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl) {
  ScopeMap scope = BuildParamScope(mod);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& [path_expr, val_expr] : item->defparam_assigns) {
      RtlirModule* target_mod = nullptr;
      auto* param = ResolveDefparamPath(mod, path_expr, &target_mod);
      if (!param) {
        diag_.Warning(item->loc, "defparam target not found");
        continue;
      }
      if (param->is_type_param) {
        diag_.Error(item->loc, "defparam cannot override a type parameter");
        continue;
      }
      if (param->is_localparam) {
        diag_.Error(item->loc, "defparam cannot override a local parameter");
        continue;
      }
      auto val = ConstEvalInt(val_expr, scope);
      if (!val) {
        diag_.Warning(item->loc, "defparam value is not constant");
        continue;
      }
      // §23.10: defparam wins over a module instance parameter assignment.
      param->resolved_value = ConvertOverrideValue(*val, *param);
      param->is_resolved = true;
      param->from_override = true;
      // §23.10.3: recompute dependent parameters now that the source changed.
      RecomputeDependentParams(target_mod);
    }
  }
}

void Elaborator::ApplyDefparamsRecursively(RtlirModule* mod) {
  if (!mod) return;
  if (auto* decl = FindModule(mod->name)) {
    ApplyDefparams(mod, decl);
  }
  for (auto& child : mod->children) {
    ApplyDefparamsRecursively(child.resolved);
  }
}

}  // namespace delta
