#include "elaborator/interface_property_instance.h"

#include <string>
#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

const ModuleDecl* FindInterface(std::string_view name,
                                const CompilationUnit* unit) {
  for (const ModuleDecl* ifc : unit->interfaces) {
    if (ifc->name == name) return ifc;
  }
  return nullptr;
}

// The names `e` reads without a hierarchical path: every identifier but the
// member a `.` or `::` selects.
void CollectFreeNames(const Expr* e,
                      std::unordered_set<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.insert(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectFreeNames(e->lhs, out);
    return;
  }
  const Expr* children[] = {
      e->lhs,       e->rhs,       e->base,       e->index,        e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count, e->with_expr};
  for (const Expr* c : children) CollectFreeNames(c, out);
  for (const Expr* a : e->args) CollectFreeNames(a, out);
  for (const Expr* el : e->elements) CollectFreeNames(el, out);
}

Expr* InstanceMember(std::string_view inst, std::string_view name,
                     SourceLoc loc, Arena& arena) {
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = inst;
  base->range.start = loc;
  auto* member = arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = name;
  member->range.start = loc;
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = base;
  access->rhs = member;
  access->range.start = loc;
  return access;
}

// `decl` as instance `inst` of its interface sees it: named "inst.name",
// with each name its body reads, a formal aside, made the member of `inst`
// that §23.6 reaches by the path.
ModuleItem* InstanceCopy(const ModuleItem* decl, std::string_view inst,
                         Arena& arena) {
  std::unordered_set<std::string_view> names;
  CollectFreeNames(decl->prop_body_expr, names);
  CollectFreeNames(decl->prop_disable_iff, names);
  for (const EventExpr& ev : decl->prop_clock) {
    CollectFreeNames(ev.signal, names);
    CollectFreeNames(ev.iff_condition, names);
  }
  for (std::string_view formal : decl->prop_formals) names.erase(formal);
  ActualsByFormal members;
  for (std::string_view name : names) {
    members[name] = InstanceMember(inst, name, decl->loc, arena);
  }
  auto* copy = arena.Create<ModuleItem>(*decl);
  copy->name = *arena.Create<std::string>(std::string(inst) + "." +
                                          std::string(decl->name));
  copy->prop_body_expr =
      SubstituteFormals(decl->prop_body_expr, members, arena);
  copy->prop_disable_iff =
      SubstituteFormals(decl->prop_disable_iff, members, arena);
  // The tree the parser also reads the clocked boolean form into keeps the
  // interface's own names, so the copy is evaluated as the boolean alone.
  copy->prop_body_tree = nullptr;
  for (EventExpr& ev : copy->prop_clock) {
    ev.signal = SubstituteFormals(ev.signal, members, arena);
    ev.iff_condition = SubstituteFormals(ev.iff_condition, members, arena);
  }
  return copy;
}

}  // namespace

void RegisterInterfaceInstanceProperties(const ModuleDecl* decl,
                                         const CompilationUnit* unit,
                                         PropertyRegistry& registry,
                                         Arena& arena) {
  if (decl == nullptr || unit == nullptr) return;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    const ModuleDecl* ifc = FindInterface(item->inst_module, unit);
    if (ifc == nullptr) continue;
    for (const ModuleItem* member : ifc->items) {
      if (member->kind != ModuleItemKind::kPropertyDecl ||
          member->prop_body_expr == nullptr) {
        continue;
      }
      registry.Register(InstanceCopy(member, item->inst_name, arena));
    }
  }
}

}  // namespace delta
