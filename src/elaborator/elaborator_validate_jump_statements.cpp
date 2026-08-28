// §12.8 "Jump statements" — the elaboration-time rules for break, continue and
// return, together with the one clause that gives two of them another meaning:
// §18.17.6 "Aborting productions—break and return". Split out of
// elaborator_validate_funcchecks.cpp, which keeps §12.7.3's foreach rules and
// §13.4.3's constant-function rules.

#include <format>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §18.17.6 says of break and return that "these two statements can appear in
// any code block; they differ in what they consider the scope from which to
// exit". This is that scope, as the two clauses that give a jump statement a
// meaning describe it: what encloses the statement being walked.
struct JumpScope {
  // §12.8: "The continue and break statements can only be used in a loop."
  // Counts the enclosing loops a jump reaches without crossing a fork-join
  // boundary.
  int loop_depth = 0;
  // §12.8: "The continue and break statements cannot be used inside a
  // fork-join block to control a loop outside the fork-join block." Counts the
  // enclosing fork-join blocks.
  int fork_depth = 0;
  // §12.8: "The return statement can only be used in a subroutine." True when
  // the walk started in a function or task body.
  bool in_subroutine = false;
  // §18.17.6: inside a randsequence production code block, break "forces a
  // jump out of the randsequence block" and return "aborts the generation of
  // the current production". Neither needs the enclosing loop or the enclosing
  // subroutine §12.8 asks for, so this term is what withholds those two
  // reports. It stays set through a fork-join written inside the code block:
  // §12.8's fork sentence is about controlling a loop outside the fork-join
  // block, and the randsequence block a break leaves is not a loop.
  bool in_production_code_block = false;
};

void CheckJumpRules(const Stmt* s, const JumpScope& scope, DiagEngine& diag);

// §12.8 — a break shall stand in a loop, and not in a fork-join block that
// the loop it breaks encloses. §18.17.6 gives it a randsequence block to leave
// instead where it stands in a production code block, so no loop is required
// there; where that code block writes a loop of its own, §12.8 binds the break
// to it, which is why `loop_depth` is still counted inside a production rather
// than reset.
//
// A break in a production code block whose only enclosing loop stands outside
// the randsequence block binds to the randsequence block and not to that loop.
// §18.17.6 states without qualification that "when a break statement is
// executed from within a production code block, it forces a jump out of the
// randsequence block", and the "within a loop statement" sentence that defers
// to §12.8 is about a loop the code block itself writes. Elaboration accepts
// the source on either reading, one clause finding a production and the other
// a loop, so what fixes the reading is this comment and
// JumpStatementElaboration.BreakInARandsequenceProductionCodeBlockInsideAnOuterLoopOk
// in test/src/unit/test_elaborator_subclause_12_08.cpp; the randsequence
// executor is where the difference is observable.
void CheckBreakScope(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  if (scope.loop_depth > 0 || scope.in_production_code_block) return;
  if (scope.fork_depth > 0) {
    diag.Error(s->range.start,
               "break inside fork-join cannot exit a loop outside the "
               "fork-join block",
               Subclause("12.8"));
    return;
  }
  diag.Error(s->range.start, "break statement is not inside a loop",
             Subclause("12.8"));
}

// §12.8 — the same two rules for continue, with no §18.17.6 term: that clause
// names break and return and says nothing of continue, so a continue in a
// production code block still has to stand in a loop.
void CheckContinueScope(const Stmt* s, const JumpScope& scope,
                        DiagEngine& diag) {
  if (scope.loop_depth > 0) return;
  if (scope.fork_depth > 0) {
    diag.Error(s->range.start,
               "continue inside fork-join cannot affect a loop outside "
               "the fork-join block",
               Subclause("12.8"));
    return;
  }
  diag.Error(s->range.start, "continue statement is not inside a loop",
             Subclause("12.8"));
}

// Returns true when `s` is itself a jump leaf (break/continue/return) and
// reports any §12.8 violation for it. Caller stops descending on true.
bool CheckJumpLeaf(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  switch (s->kind) {
    case StmtKind::kBreak:
      CheckBreakScope(s, scope, diag);
      return true;
    case StmtKind::kContinue:
      CheckContinueScope(s, scope, diag);
      return true;
    case StmtKind::kReturn:
      // §18.17.6: a return in a production code block aborts the production
      // rather than a subroutine, so §12.8's subroutine requirement is not
      // what governs it.
      if (!scope.in_subroutine && !scope.in_production_code_block) {
        diag.Error(s->range.start,
                   "return statement is only allowed inside a subroutine",
                   Subclause("12.8"));
      }
      return true;
    default:
      return false;
  }
}

bool IsLoopStmtKind(StmtKind k) {
  return k == StmtKind::kFor || k == StmtKind::kForeach ||
         k == StmtKind::kWhile || k == StmtKind::kForever ||
         k == StmtKind::kRepeat || k == StmtKind::kDoWhile;
}

// Recurses into every generic child statement of `s` carrying the current
// jump scope unchanged (used for non-loop, non-fork statements), and into the
// randsequence production code blocks with the §18.17.6 term set.
//
// The generic links are still written out here rather than taken from
// ForEachChildStmt in elaborator_validate_internal.h. That conversion is
// #3301's, and it also brings Stmt::body, Stmt::for_body, Stmt::fork_stmts,
// Stmt::for_inits and Stmt::for_steps, each of which this walk already reaches
// with a scope of its own; folding them into one list is a separate question
// from the two lists below.
void CheckJumpRulesChildren(const Stmt* s, const JumpScope& scope,
                            DiagEngine& diag) {
  for (auto* sub : s->stmts) CheckJumpRules(sub, scope, diag);
  CheckJumpRules(s->then_branch, scope, diag);
  CheckJumpRules(s->else_branch, scope, diag);
  for (auto& ci : s->case_items) CheckJumpRules(ci.body, scope, diag);
  for (auto& ri : s->randcase_items) CheckJumpRules(ri.second, scope, diag);
  CheckJumpRules(s->assert_pass_stmt, scope, diag);
  CheckJumpRules(s->assert_fail_stmt, scope, diag);

  // §18.17.6 gives break and return a meaning in a randsequence production
  // code block that they have nowhere else, so the two statement lists
  // Stmt::rs_productions reaches are walked with that term set.
  // ForEachRandsequenceStmt in elaborator_validate_internal.h hands over both
  // of them: A.6.12's rs_prod may be an rs_code_block, whose statements the
  // parser keeps in RsProd::code_stmts, and A.6.12's rs_rule admits a second
  // rs_code_block after a weight_specification, whose statements go in
  // RsRule::weight_code.
  JumpScope production = scope;
  production.in_production_code_block = true;
  ForEachRandsequenceStmt(
      s, [&](Stmt* const& sub) { CheckJumpRules(sub, production, diag); });
}

// Walks one statement subtree enforcing §12.8's rules for break, continue and
// return, and §18.17.6's exemption from two of them.
void CheckJumpRules(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  if (!s) return;

  if (CheckJumpLeaf(s, scope, diag)) return;

  if (IsLoopStmtKind(s->kind)) {
    JumpScope inner = scope;
    inner.loop_depth = scope.loop_depth + 1;
    CheckJumpRules(s->body, inner, diag);
    CheckJumpRules(s->for_body, inner, diag);
    for (auto* init : s->for_inits) CheckJumpRules(init, scope, diag);
    for (auto* step : s->for_steps) CheckJumpRules(step, scope, diag);
    return;
  }

  if (s->kind == StmtKind::kFork) {
    JumpScope inner = scope;
    inner.loop_depth = 0;
    inner.fork_depth = scope.fork_depth + 1;
    for (auto* sub : s->fork_stmts) CheckJumpRules(sub, inner, diag);
    return;
  }

  CheckJumpRulesChildren(s, scope, diag);
}

// Map literal expression kinds whose type is obvious from the syntax alone
// to the corresponding DataTypeKind. Returns kImplicit when no narrow
// classification is possible without full expression type inference.
DataTypeKind ObviousLiteralKind(const Expr* e) {
  if (!e) return DataTypeKind::kImplicit;
  switch (e->kind) {
    case ExprKind::kStringLiteral:
      return DataTypeKind::kString;
    case ExprKind::kRealLiteral:
      return DataTypeKind::kReal;
    case ExprKind::kIntegerLiteral:
      return DataTypeKind::kInt;
    case ExprKind::kTimeLiteral:
      return DataTypeKind::kTime;
    default:
      return DataTypeKind::kImplicit;
  }
}

// In a value-returning function, a return statement shall carry an
// expression of the correct type. The void-with-expression case is
// reported elsewhere; the type check here catches narrow but clearly
// wrong mismatches (string-vs-integral, real-vs-string, etc.).
void CheckValueReturningFuncReturn(const Stmt* s, std::string_view func_name,
                                   const DataType& return_type,
                                   DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    if (s->expr == nullptr) {
      diag.Error(s->range.start,
                 std::format("return statement in non-void function '{}' "
                             "shall have an expression",
                             func_name),
                 Subclause("12.8"));
      return;
    }
    DataTypeKind expr_kind = ObviousLiteralKind(s->expr);
    if (expr_kind != DataTypeKind::kImplicit) {
      DataType expr_type;
      expr_type.kind = expr_kind;
      if (!IsAssignmentCompatible(return_type, expr_type)) {
        diag.Error(s->range.start,
                   std::format("return expression in function '{}' is not "
                               "assignment-compatible with the function's "
                               "return type",
                               func_name),
                   Subclause("12.8"));
      }
    }
    return;
  }
  // Stmt::rs_productions is left out of this walk, and #3301's conversion onto
  // ForEachChildStmt is held back for it: §18.17.6 makes a return in a
  // randsequence production code block abort the production rather than the
  // enclosing function, so it is not the function's return and §12.8's
  // "in a function returning a value, the return statement shall have an
  // expression of the correct type" is not about it.
  for (auto* sub : s->stmts)
    CheckValueReturningFuncReturn(sub, func_name, return_type, diag);
  for (auto* sub : s->fork_stmts)
    CheckValueReturningFuncReturn(sub, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->then_branch, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->else_branch, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->body, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->for_body, func_name, return_type, diag);
  for (auto& ci : s->case_items)
    CheckValueReturningFuncReturn(ci.body, func_name, return_type, diag);
  for (auto& ri : s->randcase_items)
    CheckValueReturningFuncReturn(ri.second, func_name, return_type, diag);
  CheckValueReturningFuncReturn(s->assert_pass_stmt, func_name, return_type,
                                diag);
  CheckValueReturningFuncReturn(s->assert_fail_stmt, func_name, return_type,
                                diag);
}

// §12.8 — applies the jump rules to a function/task body and, for a
// value-returning function, also checks each return statement's expression.
void CheckSubroutineJumpRules(const ModuleItem* item, DiagEngine& diag) {
  bool is_value_returning = false;
  if (item->kind == ModuleItemKind::kFunctionDecl) {
    is_value_returning = (item->return_type.kind != DataTypeKind::kVoid);
  }
  JumpScope scope;
  scope.in_subroutine = true;
  for (auto* s : item->func_body_stmts) {
    CheckJumpRules(s, scope, diag);
    if (is_value_returning) {
      CheckValueReturningFuncReturn(s, item->name, item->return_type, diag);
    }
  }
}

}  // namespace

void Elaborator::ValidateJumpStatements(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind) && item->body) {
      CheckJumpRules(item->body, JumpScope{}, diag_);
      continue;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      CheckSubroutineJumpRules(item, diag_);
    }
  }
}

}  // namespace delta
