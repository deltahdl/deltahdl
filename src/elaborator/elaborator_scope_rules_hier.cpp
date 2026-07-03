#include <algorithm>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

// Local copy of the procedural-block predicate (the primary definition lives in
// elaborator_scope_rules.cpp); both files need it and it is too small to
// warrant a shared header.
bool IsProcBodyItem(ModuleItemKind k) {
  return k == ModuleItemKind::kInitialBlock ||
         k == ModuleItemKind::kFinalBlock ||
         k == ModuleItemKind::kAlwaysBlock ||
         k == ModuleItemKind::kAlwaysCombBlock ||
         k == ModuleItemKind::kAlwaysFFBlock ||
         k == ModuleItemKind::kAlwaysLatchBlock;
}

void CollectMemberAccess(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) {
    out.push_back(e);
  }
  CollectMemberAccess(e->lhs, out);
  CollectMemberAccess(e->rhs, out);
  CollectMemberAccess(e->base, out);
  CollectMemberAccess(e->index, out);
  CollectMemberAccess(e->index_end, out);
  CollectMemberAccess(e->condition, out);
  CollectMemberAccess(e->true_expr, out);
  CollectMemberAccess(e->false_expr, out);
  CollectMemberAccess(e->repeat_count, out);
  CollectMemberAccess(e->with_expr, out);
  for (const auto* a : e->args) CollectMemberAccess(a, out);
  for (const auto* el : e->elements) CollectMemberAccess(el, out);
}

void CollectMemberAccessInStmt(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  CollectMemberAccess(s->condition, out);
  CollectMemberAccess(s->lhs, out);
  CollectMemberAccess(s->rhs, out);
  CollectMemberAccess(s->delay, out);
  CollectMemberAccess(s->cycle_delay, out);
  CollectMemberAccess(s->for_cond, out);
  CollectMemberAccess(s->expr, out);
  CollectMemberAccess(s->assert_expr, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) CollectMemberAccess(p, out);
    CollectMemberAccessInStmt(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    CollectMemberAccess(w, out);
    CollectMemberAccessInStmt(body, out);
  }
  for (const auto* sub : s->stmts) CollectMemberAccessInStmt(sub, out);
  for (const auto* sub : s->fork_stmts) CollectMemberAccessInStmt(sub, out);
  CollectMemberAccessInStmt(s->then_branch, out);
  CollectMemberAccessInStmt(s->else_branch, out);
  CollectMemberAccessInStmt(s->body, out);
  CollectMemberAccessInStmt(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectMemberAccessInStmt(fi, out);
  for (const auto* fs : s->for_steps) CollectMemberAccessInStmt(fs, out);
  CollectMemberAccessInStmt(s->assert_pass_stmt, out);
  CollectMemberAccessInStmt(s->assert_fail_stmt, out);
}

struct InstanceArrayBounds {
  int64_t low;
  int64_t high;
};

bool DecodeInstanceArrayBase(const Expr* ma, std::string_view& name,
                             const Expr*& select_index) {
  if (!ma || ma->kind != ExprKind::kMemberAccess || !ma->lhs) return false;
  const Expr* base = ma->lhs;
  if (base->kind == ExprKind::kIdentifier) {
    name = base->text;
    select_index = nullptr;
    return true;
  }
  if (base->kind == ExprKind::kSelect && base->base &&
      base->base->kind == ExprKind::kIdentifier) {
    name = base->base->text;
    select_index = base->index;
    return true;
  }
  return false;
}

void CollectModuleMemberAccesses(const ModuleDecl* decl,
                                 std::vector<const Expr*>& accesses) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProcBodyItem(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }
}

bool ImportWildcardProvides(const CompilationUnit* unit,
                            std::string_view package_name,
                            std::string_view name) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name != package_name) continue;
    for (const auto* pi : pkg->items) {
      if (pi->name == name) return true;
      if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
          pi->class_decl->name == name) {
        return true;
      }
    }
  }
  return false;
}

bool ImportedIntoModule(const CompilationUnit* unit, const RtlirModule* m,
                        std::string_view name) {
  for (const auto& imp : m->imports) {
    if (!imp.is_wildcard && imp.item_name == name) return true;
    if (imp.is_wildcard &&
        ImportWildcardProvides(unit, imp.package_name, name)) {
      return true;
    }
  }
  return false;
}

void CheckHierRefImportedMemberAccess(
    DiagEngine& diag, const CompilationUnit* unit,
    const std::unordered_map<std::string_view, const RtlirModule*>& inst_type,
    const Expr* ma) {
  if (!ma || ma->kind != ExprKind::kMemberAccess) return;
  if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
  if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
  auto it = inst_type.find(ma->lhs->text);
  if (it == inst_type.end()) return;
  if (ImportedIntoModule(unit, it->second, ma->rhs->text)) {
    diag.Error(
        ma->range.start,
        std::format("hierarchical reference '{}.{}' targets a name imported "
                    "into '{}' from a package; imported names are not "
                    "visible through hierarchical references",
                    ma->lhs->text, ma->rhs->text, it->second->name));
  }
}

std::unordered_map<std::string_view, const RtlirModule*>
CollectResolvedChildren(const RtlirModule* mod) {
  std::unordered_map<std::string_view, const RtlirModule*> inst_type;
  for (const auto& child : mod->children) {
    if (child.resolved) inst_type[child.inst_name] = child.resolved;
  }
  return inst_type;
}

// True when any element of `range` projects (via `proj`) to `name`.
template <typename Range, typename Proj>
bool RangeHasName(const Range& range, Proj proj, std::string_view name) {
  for (const auto& e : range) {
    if (proj(e) == name) return true;
  }
  return false;
}

bool EnumTypesDeclare(const RtlirModule* m, std::string_view name) {
  for (const auto& entry : m->enum_types) {
    if (RangeHasName(
            entry.second, [](const RtlirEnumMember& e) { return e.name; },
            name)) {
      return true;
    }
  }
  return false;
}

// True when `name` is declared at the top level of module `m` and so may be the
// target of a hierarchical reference `inst.name`. Covers every flat namespace
// an instance member access can reach.
bool ModuleDeclaresMember(const RtlirModule* m, std::string_view name) {
  auto ptr_name = [](const auto* d) {
    return d ? d->name : std::string_view{};
  };
  return RangeHasName(
             m->ports, [](const RtlirPort& p) { return p.name; }, name) ||
         RangeHasName(
             m->nets, [](const RtlirNet& n) { return n.name; }, name) ||
         RangeHasName(
             m->variables, [](const RtlirVariable& v) { return v.name; },
             name) ||
         RangeHasName(
             m->params, [](const RtlirParamDecl& p) { return p.name; }, name) ||
         RangeHasName(m->function_decls, ptr_name, name) ||
         RangeHasName(m->let_decls, ptr_name, name) ||
         RangeHasName(m->sequence_decls, ptr_name, name) ||
         RangeHasName(m->class_decls, ptr_name, name) ||
         RangeHasName(
             m->children, [](const RtlirModuleInst& c) { return c.inst_name; },
             name) ||
         EnumTypesDeclare(m, name);
}

// Gate for the undeclared-member check: only a plain module whose top-level
// namespace is fully enumerable by ModuleDeclaresMember may be checked.
// Interfaces and programs expose modports/clocking-block members; a generate
// construct introduces named scopes; and a procedural block can declare named
// blocks (`begin : label`) reachable hierarchically — none of which appear in
// the flat RtlirModule lists. For any of those the check is suppressed so it
// never produces a false positive.
bool ChildDeclAllowsMemberCheck(const ModuleDecl* child) {
  if (!child) return false;
  if (child->decl_kind != ModuleDeclKind::kModule) return false;
  if (!child->modports.empty()) return false;
  for (const auto* item : child->items) {
    if (IsProcBodyItem(item->kind)) return false;
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      return false;
    }
  }
  return true;
}

std::unordered_map<std::string_view, InstanceArrayBounds>
CollectInstanceArrayBounds(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, InstanceArrayBounds> arrayed;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (!item->inst_range_left || !item->inst_range_right) continue;
    auto lhi = ConstEvalInt(item->inst_range_left);
    auto rhi = ConstEvalInt(item->inst_range_right);
    if (!lhi || !rhi) continue;
    InstanceArrayBounds b;
    b.low = std::min(*lhi, *rhi);
    b.high = std::max(*lhi, *rhi);
    arrayed[item->inst_name] = b;
  }
  return arrayed;
}

void CheckHierRefInstanceArrayAccess(
    DiagEngine& diag,
    const std::unordered_map<std::string_view, InstanceArrayBounds>& arrayed,
    const Expr* ma, const ScopeMap& scope) {
  std::string_view name;
  const Expr* select_index = nullptr;
  if (!DecodeInstanceArrayBase(ma, name, select_index)) return;
  auto it = arrayed.find(name);
  if (it == arrayed.end()) return;
  if (!select_index) {
    diag.Error(ma->range.start,
               std::format("hierarchical reference to instance array '{}' "
                           "requires an instance select",
                           name));
    return;
  }
  // §23.6: the instance select is a constant expression, so it may be any of
  // the constant forms of 11.2.1 -- a literal, but equally a parameter or
  // localparam. Evaluate it against the enclosing module's parameter scope so a
  // parameter-valued select is range-checked, not just a bare literal.
  auto idx = ConstEvalInt(select_index, scope);
  if (!idx) return;
  if (*idx < it->second.low || *idx > it->second.high) {
    diag.Error(select_index->range.start,
               std::format("instance select [{}] is out of range for "
                           "instance array '{}' [{}:{}]",
                           *idx, name, it->second.high, it->second.low));
  }
}

}  // namespace

// §23.6: a hierarchical reference `inst.name` into a resolved child of a plain
// module (see ChildDeclAllowsMemberCheck) is unresolved when the child does not
// declare `name`. The imported-name case is reported by the imported-member
// check above, so it is skipped here to avoid a duplicate diagnostic.
void Elaborator::CheckHierRefUndeclaredMember(
    const std::unordered_map<std::string_view, const RtlirModule*>& inst_type,
    const Expr* ma) {
  if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
  if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
  auto it = inst_type.find(ma->lhs->text);
  if (it == inst_type.end()) return;
  if (!ChildDeclAllowsMemberCheck(FindModule(it->second->name))) return;
  if (ModuleDeclaresMember(it->second, ma->rhs->text)) return;
  if (ImportedIntoModule(unit_, it->second, ma->rhs->text)) return;
  diag_.Error(
      ma->range.start,
      std::format("hierarchical reference '{}.{}' is unresolved: '{}' is not "
                  "declared in module '{}'",
                  ma->lhs->text, ma->rhs->text, ma->rhs->text,
                  it->second->name));
}

void Elaborator::ValidateHierRefToImportedName(const ModuleDecl* decl,
                                               const RtlirModule* mod) {
  if (!mod || mod->children.empty()) return;
  std::unordered_map<std::string_view, const RtlirModule*> inst_type =
      CollectResolvedChildren(mod);
  if (inst_type.empty()) return;

  std::vector<const Expr*> accesses;
  CollectModuleMemberAccesses(decl, accesses);
  for (const auto* ma : accesses) {
    CheckHierRefImportedMemberAccess(diag_, unit_, inst_type, ma);
    CheckHierRefUndeclaredMember(inst_type, ma);
  }
}

void Elaborator::ValidateHierRefInstanceArray(const ModuleDecl* decl,
                                              const RtlirModule* mod) {
  std::unordered_map<std::string_view, InstanceArrayBounds> arrayed =
      CollectInstanceArrayBounds(decl);
  if (arrayed.empty()) return;

  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  std::vector<const Expr*> accesses;
  CollectModuleMemberAccesses(decl, accesses);
  for (const auto* ma : accesses) {
    CheckHierRefInstanceArrayAccess(diag_, arrayed, ma, scope);
  }
}

}  // namespace delta
