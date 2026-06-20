#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

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

static bool RhsContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty()) return true;
  if (RhsContainsHierarchicalRef(e->lhs)) return true;
  if (RhsContainsHierarchicalRef(e->rhs)) return true;
  if (RhsContainsHierarchicalRef(e->base)) return true;
  if (RhsContainsHierarchicalRef(e->index)) return true;
  if (RhsContainsHierarchicalRef(e->index_end)) return true;
  if (RhsContainsHierarchicalRef(e->condition)) return true;
  if (RhsContainsHierarchicalRef(e->true_expr)) return true;
  if (RhsContainsHierarchicalRef(e->false_expr)) return true;
  if (RhsContainsHierarchicalRef(e->repeat_count)) return true;
  for (const auto* a : e->args) {
    if (RhsContainsHierarchicalRef(a)) return true;
  }
  for (const auto* elem : e->elements) {
    if (RhsContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

RtlirParamDecl* Elaborator::ResolveDefparamPath(RtlirModule* root,
                                                const Expr* path_expr,
                                                RtlirModule** out_mod) {
  std::vector<std::string_view> parts;
  CollectPathComponents(path_expr, parts);
  if (parts.size() < 2) return nullptr;

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
    for (size_t idx = 0; idx < item->defparam_assigns.size(); ++idx) {
      auto key = std::make_tuple(mod, item, idx);
      if (applied_defparams_.count(key)) continue;
      const auto& [path_expr, val_expr] = item->defparam_assigns[idx];
      RtlirModule* target_mod = nullptr;
      auto* param = ResolveDefparamPath(mod, path_expr, &target_mod);
      if (!param) continue;
      if (param->is_type_param) {
        diag_.Error(item->loc, "defparam cannot override a type parameter");
        applied_defparams_.insert(key);
        continue;
      }
      if (param->is_localparam) {
        diag_.Error(item->loc, "defparam cannot override a local parameter");
        applied_defparams_.insert(key);
        continue;
      }
      if (param->config_locked) {
        // A configuration's parameter override takes precedence over a defparam
        // targeting the same parameter (§33.4.3); leave the config value in
        // place and treat this defparam as resolved against it.
        applied_defparams_.insert(key);
        continue;
      }
      if (RhsContainsHierarchicalRef(val_expr)) {
        diag_.Error(item->loc,
                    "defparam right-hand side may only reference parameters "
                    "declared in the same module");
        applied_defparams_.insert(key);
        continue;
      }
      auto val = ConstEvalInt(val_expr, scope);
      if (!val) {
        diag_.Warning(item->loc, "defparam value is not constant");
        applied_defparams_.insert(key);
        continue;
      }

      param->resolved_value = ConvertOverrideValue(*val, *param);
      param->is_resolved = true;
      param->from_override = true;

      RecomputeDependentParams(target_mod);
      applied_defparams_.insert(key);
      early_defparam_resolutions_.push_back({mod, path_expr, param, item->loc});
    }
  }
}

void Elaborator::VerifyEarlyResolvedDefparams() {
  for (const auto& rec : early_defparam_resolutions_) {
    auto* now = ResolveDefparamPath(rec.root, rec.path_expr);
    if (now != nullptr && now != rec.resolved) {
      diag_.Error(rec.loc,
                  "defparam hierarchical name resolves differently after "
                  "full elaboration than during early resolution");
    }
  }
}

// Names of the generate blocks a conditional/loop generate construct can
// introduce directly into the enclosing scope. A conditional construct
// contributes its then-block name plus, recursively, the names of every
// else/else-if alternative; a case construct contributes each item label; a
// loop construct contributes its array name.
static void CollectLocalGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty()) out.insert(item->name);
      if (item->gen_else) CollectLocalGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items)
        if (!ci.label.empty()) out.insert(ci.label);
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty()) out.insert(item->name);
      break;
    default:
      break;
  }
}

// §23.10.4.2: a defparam's hierarchical name may have to be resolved before the
// hierarchy is fully elaborated (so a generate condition that reads the target
// can be evaluated). If that early resolution would differ from the resolution
// the completed hierarchy dictates, it is an error. The situation arises when a
// named generate block in the module holding the defparam shares its name with
// a scope named by the leading component of the defparam's path: before the
// block is elaborated the leading name resolves outward (here, to a top-level
// module of the same name), but once the block exists the same name would bind
// to the local block instead, changing the target. We flag that collision; per
// the LRM it is fixed by renaming the generate block.
void Elaborator::CheckEarlyResolutionAmbiguity(
    RtlirModule* mod, const std::unordered_set<std::string_view>& top_names) {
  if (!mod) return;
  const auto* decl = FindModule(mod->name);
  if (!decl) return;

  std::unordered_set<std::string_view> block_names;
  for (const auto* item : decl->items)
    CollectLocalGenerateBlockNames(item, block_names);
  if (block_names.empty()) return;

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& assign : item->defparam_assigns) {
      std::vector<std::string_view> parts;
      CollectPathComponents(assign.first, parts);
      if (parts.size() < 2) continue;
      auto lead = parts.front();
      if (block_names.count(lead) && top_names.count(lead)) {
        diag_.Error(item->loc,
                    "defparam hierarchical name would resolve differently once "
                    "the like-named generate block is elaborated");
      }
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

void Elaborator::WarnUnresolvedDefparams(RtlirModule* mod) {
  if (!mod) return;
  if (auto* decl = FindModule(mod->name)) {
    for (const auto* item : decl->items) {
      if (item->kind != ModuleItemKind::kDefparam) continue;
      for (size_t idx = 0; idx < item->defparam_assigns.size(); ++idx) {
        auto key = std::make_tuple(mod, item, idx);
        if (!applied_defparams_.count(key)) {
          diag_.Warning(item->loc, "defparam target not found");
        }
      }
    }
  }
  for (auto& child : mod->children) {
    WarnUnresolvedDefparams(child.resolved);
  }
}

}  // namespace delta
