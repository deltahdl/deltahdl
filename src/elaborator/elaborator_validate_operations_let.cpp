#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

// §11.12's rules on where a let may be referred to: before its declaration in
// no scope, and through a hierarchical name nowhere.

namespace delta {

namespace {

// Runs `fn` over `e` and every expression under it, the member a member
// access selects excepted: `h.tmp` and `L0[0].L1.my_let` name `tmp` and
// `my_let` within the scope their prefix names, not the scope written in.
template <typename Fn>
void ForEachExprUnder(const Expr* e, Fn& fn) {
  if (e == nullptr) return;
  fn(e);
  if (e->kind == ExprKind::kMemberAccess) {
    ForEachExprUnder(e->lhs, fn);
    return;
  }
  ForEachExprChild(e,
                   [&fn](const Expr* child) { ForEachExprUnder(child, fn); });
}

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

// The same rule within each begin-end or fork block under `s`, whose lets are
// declared among its statements as block item declarations.
void CheckBlockLetsUsedBeforeDeclared(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr) return;
  LetPositions scope;
  for (size_t i = 0; i < s->stmts.size(); ++i) {
    const Stmt* sub = s->stmts[i];
    if (sub->kind == StmtKind::kBlockItemDecl &&
        sub->decl_item->kind == ModuleItemKind::kLetDecl)
      scope.let_at.emplace(sub->decl_item->name, i);
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
  auto check = [&](const Expr* e) {
    if (e->kind != ExprKind::kCall || e->lhs == nullptr ||
        e->lhs->kind != ExprKind::kMemberAccess || e->lhs->rhs == nullptr ||
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

namespace {

// Whether `t` is a value an integral or a real type gives: an integer type, an
// enum, a real, or a packed structure or union, which §6.11.1 makes integral.
bool IsIntegralOrRealLike(const DataType& t) {
  if (t.kind == DataTypeKind::kStruct || t.kind == DataTypeKind::kUnion)
    return t.is_packed || t.is_soft;
  return IsIntegralType(t.kind) || IsRealType(t.kind);
}

// §6.22.4 as §11.12 asks it of an actual and its typed formal, both followed
// through their typedefs. A string on either side is left alone.
bool ActualFitsFormal(const DataType& actual, const DataType& formal) {
  if (actual.kind == DataTypeKind::kString ||
      formal.kind == DataTypeKind::kString)
    return true;
  return IsCastCompatible(actual, formal) ||
         (IsIntegralOrRealLike(actual) && IsIntegralOrRealLike(formal));
}

// A variable an actual may name, as a module or a block declares it.
struct LetActualVariable {
  const DataType* type;
  bool is_array;
};

// §11.12, rule 2, checked at each call of a let of the module and, for a
// default actual, once at the let's declaration.
class LetActualCheck {
 public:
  LetActualCheck(const TypedefMap& typedefs, DiagEngine& diag)
      : typedefs_(typedefs), diag_(diag) {}

  void Collect(const ModuleItem* item) {
    if (item->kind == ModuleItemKind::kLetDecl) lets_[item->name] = item;
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl)
      vars_[item->name] = {&item->data_type, !item->unpacked_dims.empty()};
    CollectBlockVariables(item->body);
    for (const Stmt* s : item->func_body_stmts) CollectBlockVariables(s);
  }

  void CheckDefaults() {
    for (const auto& entry : lets_) {
      for (const auto& formal : entry.second->func_args)
        CheckActual(formal.default_value, formal);
    }
  }

  void CheckCall(const Expr* e) {
    if (e->kind != ExprKind::kCall || e->lhs == nullptr ||
        e->lhs->kind != ExprKind::kIdentifier)
      return;
    auto it = lets_.find(e->callee);
    if (it == lets_.end()) return;
    const auto& formals = it->second->func_args;
    const size_t kPositional = e->args.size() - e->arg_names.size();
    for (size_t i = 0; i < formals.size(); ++i) {
      const int kAt = ResolveActualArgIndex(e, i, formals[i].name, kPositional);
      if (kAt >= 0) CheckActual(e->args[static_cast<size_t>(kAt)], formals[i]);
    }
  }

 private:
  // The variables a block or a subroutine body declares; one of a name some
  // outer declaration also has stands for both, as the walk over the calls
  // reads no scopes.
  void CollectBlockVariables(const Stmt* s) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kVarDecl)
      vars_[s->var_name] = {&s->var_decl_type, !s->var_unpacked_dims.empty()};
    ForEachChildStmt(s,
                     [this](Stmt* const& sub) { CollectBlockVariables(sub); });
  }

  // §11.12, rule 2: a typed formal other than an event takes an actual whose
  // self-determined type is cast compatible (§6.22.4) with its own -- an
  // unpacked array only for a formal of one, of an element type
  // ActualFitsFormal admits, as it admits a scalar's type -- which the
  // declared type of a variable the actual names decides. An untyped formal
  // takes any actual.
  void CheckActual(const Expr* actual, const FunctionArg& formal) {
    const DataType& written = formal.data_type;
    if (written.kind == DataTypeKind::kImplicit ||
        written.kind == DataTypeKind::kEvent || actual == nullptr ||
        actual->kind != ExprKind::kIdentifier)
      return;
    auto it = vars_.find(actual->text);
    if (it == vars_.end()) return;
    if (it->second.is_array != !formal.unpacked_dims.empty()) {
      Report(actual, formal);
      return;
    }
    const DataType* a = TypeAtChainEnd(*it->second.type, typedefs_);
    const DataType* f = TypeAtChainEnd(written, typedefs_);
    if (a == nullptr || f == nullptr || ActualFitsFormal(*a, *f)) return;
    Report(actual, formal);
  }

  void Report(const Expr* actual, const FunctionArg& formal) {
    diag_.Error(actual->range.start,
                std::format("let actual argument '{}' is not cast compatible "
                            "with the type of formal '{}'",
                            actual->text, formal.name),
                Subclause("11.12"));
  }

  const TypedefMap& typedefs_;
  DiagEngine& diag_;
  std::unordered_map<std::string_view, const ModuleItem*> lets_;
  std::unordered_map<std::string_view, LetActualVariable> vars_;
};

}  // namespace

void ElaboratorOperationRules::CheckLetActualTypes(const ModuleDecl* decl) {
  LetActualCheck check(typedefs_, diag_);
  auto collect = [&check](const ModuleItem* item) { check.Collect(item); };
  ForEachItemNested(decl->items, collect);
  check.CheckDefaults();
  auto check_call = [&check](const Expr* e) { check.CheckCall(e); };
  auto walk = [&check_call](const ModuleItem* item) {
    ForEachExprOfItem(item, check_call);
  };
  ForEachItemNested(decl->items, walk);
}

void ElaboratorOperationRules::ValidateLetScope(const ModuleDecl* decl) {
  CheckLetUsedBeforeDeclared(decl);
  CheckLetReferencedHierarchically(decl);
  CheckLetActualTypes(decl);
}

}  // namespace delta
