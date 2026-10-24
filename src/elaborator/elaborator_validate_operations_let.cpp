#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/let_actual_check.h"
#include "elaborator/net_data_type.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

// §11.12's rules on where a let may be referred to: before its declaration in
// no scope, and through a hierarchical name nowhere; and on the actuals a let's
// formals take, which let_actual_check.cpp judges.

namespace delta {

namespace {

template <typename Fn>
void ForEachExprInStmt(const Stmt* s, Fn& fn) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&fn](Expr* const& e) { ForEachExprUnder(e, fn); });
  ForEachChildStmt(s, [&fn](Stmt* const& sub) { ForEachExprInStmt(sub, fn); });
}

// Every expression one module item writes: its procedure's or subroutine's
// statements, a continuous assignment's sides and a declaration's initializer.
template <typename Fn>
void ForEachExprOfItem(const ModuleItem* item, Fn& fn) {
  ForEachExprInStmt(item->body, fn);
  for (const Stmt* s : item->func_body_stmts) ForEachExprInStmt(s, fn);
  ForEachExprUnder(item->assign_lhs, fn);
  ForEachExprUnder(item->assign_rhs, fn);
  ForEachExprUnder(item->init_expr, fn);
}

// `items` and the items of every generate block among them, in turn.
template <typename Fn>
void ForEachItemNested(const std::vector<ModuleItem*>& items, Fn& fn) {
  for (const ModuleItem* item : items) {
    if (item == nullptr) continue;
    fn(item);
    ForEachItemNested(item->gen_body, fn);
    if (item->gen_else != nullptr)
      ForEachItemNested(std::vector<ModuleItem*>{item->gen_else}, fn);
    for (const GenerateCaseItem& ci : item->gen_case_items)
      ForEachItemNested(ci.body, fn);
  }
}

// §11.12: the lets one scope declares, by the position of each among the
// scope's items or statements, and the names its other items declare.
struct LetPositions {
  std::unordered_map<std::string_view, size_t> let_at;
  std::unordered_set<std::string_view> other_names;
};

// Reports `e` where it names a let of `scope` declared after position `at`, the
// position of the item or statement `e` is written in. A name another item of
// the scope also declares is left alone, the use then being of that
// declaration.
void ReportLetUsedBefore(const Expr* e, size_t at, const LetPositions& scope,
                         DiagEngine& diag) {
  if (e->kind != ExprKind::kIdentifier) return;
  auto it = scope.let_at.find(e->text);
  if (it == scope.let_at.end() || at >= it->second ||
      scope.other_names.contains(e->text))
    return;
  diag.Error(e->range.start,
             std::format("let '{}' is used before its declaration", e->text),
             Subclause("11.12"));
}

// §11.12: whether `s` declares a let among a block's or a subroutine body's
// statements, as the parser keeps one (Parser::ParseBlockVarDecls).
bool IsBlockLet(const Stmt* s) {
  return s->kind == StmtKind::kBlockItemDecl &&
         s->decl_item->kind == ModuleItemKind::kLetDecl;
}

// The same rule within each begin-end or fork block under `s`, whose lets are
// declared among its statements as block item declarations.
void CheckBlockLetsUsedBeforeDeclared(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr) return;
  LetPositions scope;
  for (size_t i = 0; i < s->stmts.size(); ++i) {
    const Stmt* sub = s->stmts[i];
    if (IsBlockLet(sub)) scope.let_at.emplace(sub->decl_item->name, i);
  }
  for (size_t i = 0; i < s->stmts.size(); ++i) {
    auto check = [&](const Expr* e) { ReportLetUsedBefore(e, i, scope, diag); };
    ForEachExprInStmt(s->stmts[i], check);
  }
  ForEachChildStmt(s, [&diag](Stmt* const& sub) {
    CheckBlockLetsUsedBeforeDeclared(sub, diag);
  });
}

// §11.12 asks a let be declared before it is used in the scope of its
// declaration, and a generate block and a procedural block are scopes of their
// own (§27.5, §9.3.4): the rule is applied among `items`, then within each
// generate block among them and each block their statements open.
void CheckLetsUsedBeforeDeclaredIn(const std::vector<ModuleItem*>& items,
                                   DiagEngine& diag) {
  LetPositions scope;
  for (size_t i = 0; i < items.size(); ++i) {
    const ModuleItem* item = items[i];
    if (item->kind == ModuleItemKind::kLetDecl) {
      scope.let_at.emplace(item->name, i);
    } else if (!item->name.empty()) {
      scope.other_names.insert(item->name);
    }
  }
  for (size_t i = 0; i < items.size(); ++i) {
    auto check = [&](const Expr* e) { ReportLetUsedBefore(e, i, scope, diag); };
    ForEachExprOfItem(items[i], check);
  }
  for (const ModuleItem* item : items) {
    CheckLetsUsedBeforeDeclaredIn(item->gen_body, diag);
    if (item->gen_else != nullptr)
      CheckLetsUsedBeforeDeclaredIn({item->gen_else}, diag);
    for (const GenerateCaseItem& ci : item->gen_case_items)
      CheckLetsUsedBeforeDeclaredIn(ci.body, diag);
    CheckBlockLetsUsedBeforeDeclared(item->body, diag);
    for (const Stmt* s : item->func_body_stmts)
      CheckBlockLetsUsedBeforeDeclared(s, diag);
  }
}

}  // namespace

void ElaboratorOperationRules::CheckLetUsedBeforeDeclared(
    const ModuleDecl* decl) {
  CheckLetsUsedBeforeDeclaredIn(decl->items, diag_);
}

// §11.12, example d: a let is referred to only within the scope declaring it
// and the scopes nested in it, never through a hierarchical name, so a call
// through a path whose last component names a let the module declares is
// illegal.
void ElaboratorOperationRules::CheckLetReferencedHierarchically(
    const ModuleDecl* decl) {
  // §11.12 bars a hierarchical reference to any let, so the lets a path may
  // end in are this module's, at any depth of its generate blocks, and those
  // of each module, interface or program it instantiates, `u.my_let(1'b0)`.
  std::unordered_set<std::string_view> lets;
  std::unordered_set<std::string_view> instantiated;
  auto collect = [&lets](const ModuleItem* item) {
    if (item->kind == ModuleItemKind::kLetDecl) lets.insert(item->name);
  };
  auto collect_own = [&collect, &instantiated](const ModuleItem* item) {
    collect(item);
    if (item->kind == ModuleItemKind::kModuleInst)
      instantiated.insert(item->inst_module);
  };
  ForEachItemNested(decl->items, collect_own);
  for (const auto* list :
       {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
    for (const auto* child : *list) {
      if (instantiated.contains(child->name))
        ForEachItemNested(child->items, collect);
    }
  }
  if (lets.empty()) return;
  // `p::f` and `C::f` name a package's let and a class's method by scope
  // resolution (§26.3, §8.23), which is no hierarchical reference.
  auto check = [&](const Expr* e) {
    if (e->kind != ExprKind::kCall || e->lhs == nullptr ||
        e->lhs->kind != ExprKind::kMemberAccess ||
        e->lhs->is_scope_resolution || e->lhs->rhs == nullptr ||
        !lets.count(e->lhs->rhs->text))
      return;
    diag_.Error(e->range.start, "a let shall not be referenced hierarchically",
                Subclause("11.12"));
  };
  auto walk = [&check](const ModuleItem* item) {
    ForEachExprOfItem(item, check);
  };
  ForEachItemNested(decl->items, walk);
}

// §11.12, rule 2, for the calls a design element writes; let_actual_check.h
// gives the rule.
void ElaboratorOperationRules::CheckLetActualTypes(const ModuleDecl* decl) {
  const TypeShapeTables kShapes{typedefs_, td_array_dims_, class_names_};
  CheckLetActualsOfDesignElement(*decl,
                                 UnitItemsBefore(unit_, decl->range.start),
                                 {unit_, kShapes, array_arg_dim_scope_, diag_});
}

// The same rule for the compilation unit's own items and each package's,
// judged once rather than in every design element.
void ElaboratorOperationRules::CheckUnitLetActualTypes() {
  const TypeShapeTables kShapes{typedefs_, td_array_dims_, class_names_};
  CheckLetActualsOfUnitAndPackages({unit_, kShapes, cu_param_scope_, diag_});
}

void ElaboratorOperationRules::ValidateLetScope(const ModuleDecl* decl) {
  CheckLetUsedBeforeDeclared(decl);
  CheckLetReferencedHierarchically(decl);
  CheckLetActualTypes(decl);
}

}  // namespace delta
