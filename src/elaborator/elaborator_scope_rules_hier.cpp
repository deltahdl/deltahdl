#include <algorithm>
#include <cstdint>
#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

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

// Collects every member access written anywhere in `s` and its nested
// statements. §23.6 says a hierarchical name may be written wherever the object
// it names is referenced, and §26.3 bars a hierarchical reference into an
// importing scope with no condition on where that reference stands, so every
// position a statement holds a statement in is a position both rules reach.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions
// once for the whole elaborator, which is why the list is not written out again
// here. The visitor takes `Stmt* const&` because `s` is a `const Stmt*`, which
// is how ForEachChildStmt lets a walk that only reads the tree share its list
// with the walks that rewrite it.
//
// The two loops above the call read expressions rather than statements: a case
// item's patterns and a randcase item's weight are the only expressions Stmt
// holds outside its own scalar fields, and ForEachChildStmt reaches neither
// because neither is a statement.
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
  }
  for (const auto& rc : s->randcase_items) CollectMemberAccess(rc.first, out);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectMemberAccessInStmt(sub, out); });
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
    if (IsProceduralItemKind(item->kind)) {
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
                    ma->lhs->text, ma->rhs->text, it->second->name),
        Subclause("26.3"));
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
  // §23.6 forms a hierarchical name "by concatenating the names of the modules,
  // module instance names, generate blocks ... that contain it", so a parameter
  // a generate block of `m` declares is named through that block and not by
  // `inst.name`. This is asked of the parameters and of nothing else in the
  // chain below because RtlirNet::name and RtlirVariable::name carry the prefix
  // Elaborator::ScopedName added, so a block's net is already stored under a
  // name no bare identifier matches, while RtlirParamDecl::name is bare
  // whatever scope declared it.
  auto declares_module_level_param = [&] {
    for (const auto& p : m->params) {
      if (p.name != name) continue;
      if (ParamVisibleFromScopes(p.gen_block_prefix, {})) return true;
    }
    return false;
  };
  bool selected_by_a_port =
      std::any_of(m->ports.begin(), m->ports.end(),
                  [&](const RtlirPort& p) { return PortSelectsFrom(p, name); });
  return selected_by_a_port ||
         RangeHasName(
             m->ports, [](const RtlirPort& p) { return p.name; }, name) ||
         RangeHasName(
             m->nets, [](const RtlirNet& n) { return n.name; }, name) ||
         RangeHasName(
             m->variables, [](const RtlirVariable& v) { return v.name; },
             name) ||
         declares_module_level_param() ||
         RangeHasName(m->function_decls, ptr_name, name) ||
         RangeHasName(m->let_decls, ptr_name, name) ||
         RangeHasName(m->dpi_import_decls, ptr_name, name) ||
         RangeHasName(m->sequence_decls, ptr_name, name) ||
         RangeHasName(m->class_decls, ptr_name, name) ||
         RangeHasName(
             m->children, [](const RtlirModuleInst& c) { return c.inst_name; },
             name) ||
         // §14.3 with §23.6 (printed page 354 and 741): a clocking block is a
         // named item of the module declaring it, so `u.cb` names u's block
         // and `u.cb.d` its clockvar. Asked of no clocking block, the name
         // was reported undeclared in the module that declares it.
         RangeHasName(m->clocking_blocks, ptr_name, name) ||
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
    if (IsProceduralItemKind(item->kind)) return false;
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
                           name),
               Subclause("23.6"));
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
                           *idx, name, it->second.high, it->second.low),
               Subclause("23.6"));
  }
}

}  // namespace

// §23.6: a hierarchical reference `inst.name` into a resolved child of a plain
// module (see ChildDeclAllowsMemberCheck) is unresolved when the child does not
// declare `name` and no bind directive gives it one of that name. The
// imported-name case is reported by the imported-member check above, so it is
// skipped here to avoid a duplicate diagnostic.
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
  // §23.11: a bound instance stands at the end of its target scope, so `s1.c`
  // names the instance a bind directive puts in s1, which the directives have
  // not yet inserted while this module is checked.
  if (BindIntroducesName(unit_, it->second->name, ma->lhs->text, ma->rhs->text))
    return;
  diag_.Error(
      ma->range.start,
      std::format("hierarchical reference '{}.{}' is unresolved: '{}' is not "
                  "declared in module '{}'",
                  ma->lhs->text, ma->rhs->text, ma->rhs->text,
                  it->second->name),
      Subclause("23.6"));
}

UnitHierHeadNames::UnitHierHeadNames(const CompilationUnit* unit)
    : declared_(unit) {
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* scope : *scopes) AddScope(scope);
  }
  for (const ModuleItem* item : unit->cu_items) AddItem(item);
  for (const BindDirective* bd : unit->bind_directives) {
    if (bd->instantiation != nullptr) AddItem(bd->instantiation);
  }
}

// §27.6: "All unnamed generate blocks will be given the name genblk<n>", a
// name the source does not write and the elaborator gives, so one of that
// form is the name of a generate block wherever the elaborator gave it.
static bool IsImplicitGenerateBlockName(std::string_view name) {
  constexpr std::string_view kPrefix = "genblk";
  if (!name.starts_with(kPrefix) || name.size() == kPrefix.size()) return false;
  return std::all_of(name.begin() + kPrefix.size(), name.end(),
                     [](char c) { return c >= '0' && c <= '9'; });
}

bool UnitHierHeadNames::Admits(std::string_view name) const {
  return declared_.Declares(name) || scope_names_.contains(name) ||
         IsImplicitGenerateBlockName(name);
}

void UnitHierHeadNames::AddScope(const ModuleDecl* scope) {
  scope_names_.insert(scope->name);
  for (const PortDecl& port : scope->ports) scope_names_.insert(port.name);
  for (const ModportDecl* mp : scope->modports) scope_names_.insert(mp->name);
  for (const ModuleItem* item : scope->items) AddItem(item);
  for (const BindDirective* bd : scope->bind_directives) {
    if (bd->instantiation != nullptr) AddItem(bd->instantiation);
  }
}

void UnitHierHeadNames::AddItem(const ModuleItem* item) {
  if (item == nullptr) return;
  for (std::string_view name :
       {item->name, item->inst_name, item->gate_inst_name}) {
    if (!name.empty()) scope_names_.insert(name);
  }
  if (item->nested_module_decl != nullptr) AddScope(item->nested_module_decl);
  for (const ModuleItem* sub : item->gen_body) AddItem(sub);
  AddItem(item->gen_else);
  for (const auto& ci : item->gen_case_items) {
    if (!ci.label.empty()) scope_names_.insert(ci.label);
    for (const ModuleItem* sub : ci.body) AddItem(sub);
  }
  if (item->gen_init != nullptr) AddStmt(item->gen_init);
  AddStmt(item->body);
  for (const auto& arg : item->func_args) scope_names_.insert(arg.name);
  for (const Stmt* s : item->func_body_stmts) AddStmt(s);
}

void UnitHierHeadNames::AddStmt(const Stmt* s) {
  if (s == nullptr) return;
  for (std::string_view name : {s->label, s->var_name}) {
    if (!name.empty()) scope_names_.insert(name);
  }
  // §12.7.3: a foreach loop declares its loop variables, and a key of a
  // class-keyed associative array is a handle a member is selected through.
  for (std::string_view name : s->foreach_vars) {
    if (!name.empty()) scope_names_.insert(name);
  }
  if (s->decl_item != nullptr) AddItem(s->decl_item);
  ForEachChildStmt(s, [&](Stmt* const& sub) { AddStmt(sub); });
}

namespace {

// The leftmost name of the hierarchical name `e` heads, through its member
// selects and the bit-selects of an instance array, or null where it is no
// hierarchical name a scope has to answer: a `pkg::` or class scope
// resolution, a `$root.` or `$unit::` prefix, `this` or `super`, or a call.
const Expr* HierHead(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kMemberAccess) {
      if (e->is_scope_resolution) return nullptr;
      e = e->lhs;
    } else if (e->kind == ExprKind::kSelect) {
      e = e->base;
    } else {
      break;
    }
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return nullptr;
  if (!e->scope_prefix.empty() || e->text.starts_with('$')) return nullptr;
  if (e->text == "this" || e->text == "super") return nullptr;
  return e;
}

// The heads of the hierarchical names `e` holds. A `with` clause is left
// alone: an array method's reads its iterator, `item` unless it names
// another, which no scope declares (§7.12).
void CollectHierHeads(const Expr* e, std::vector<const Expr*>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kMemberAccess) {
    if (const Expr* head = HierHead(e)) out.push_back(head);
    return;
  }
  for (const Expr* child :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->repeat_count}) {
    CollectHierHeads(child, out);
  }
  for (const Expr* child : e->args) CollectHierHeads(child, out);
  for (const Expr* child : e->elements) CollectHierHeads(child, out);
}

void CollectStmtHierHeads(const Stmt* s, std::vector<const Expr*>& out) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&](const Expr* e) { CollectHierHeads(e, out); });
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectStmtHierHeads(sub, out); });
}

}  // namespace

void ReportUnresolvedHierHeads(
    const ModuleDecl* decl, const std::function<bool(std::string_view)>& admits,
    DiagEngine& diag) {
  std::vector<const Expr*> heads;
  for (const ModuleItem* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      CollectStmtHierHeads(item->body, heads);
    bool is_subroutine = item->kind == ModuleItemKind::kTaskDecl ||
                         item->kind == ModuleItemKind::kFunctionDecl;
    if (!is_subroutine || !item->method_class.empty()) continue;
    for (const Stmt* s : item->func_body_stmts) CollectStmtHierHeads(s, heads);
  }
  for (const Expr* head : heads) {
    if (admits(head->text)) continue;
    diag.Error(head->range.start,
               std::format("hierarchical name '{}' resolves to no declaration",
                           head->text),
               Subclause("23.8"));
  }
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
