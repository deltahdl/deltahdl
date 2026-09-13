#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"

namespace delta {

namespace {

// A scope randomize is a randomize_call that is not a method on a class
// object — see §A.8.2's randomize_call production and its footnote 43. The
// parser leaves `randomize` as a plain identifier, so we detect the scope
// form syntactically: either a bare callee with no member-access prefix, or
// a callee reached through the `std::` package scope. The kCall's `callee`
// field carries the simple-identifier text only, so we inspect `lhs` to
// distinguish the bare and `std::` forms from a class-method `obj.randomize`.
bool IsScopeRandomizeCall(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* lhs = expr->lhs;
  if (!lhs) return false;
  if (lhs->kind == ExprKind::kIdentifier && lhs->text == "randomize") {
    return true;
  }
  if (lhs->kind == ExprKind::kMemberAccess && lhs->rhs &&
      lhs->rhs->kind == ExprKind::kIdentifier &&
      lhs->rhs->text == "randomize" && lhs->lhs &&
      lhs->lhs->kind == ExprKind::kIdentifier && lhs->lhs->text == "std") {
    return true;
  }
  return false;
}

// Whether a scope randomize call is written through the std package, as
// std::randomize, rather than by the bare name §18.12 also allows.
bool IsStdQualifiedRandomizeCall(const Expr* expr) {
  return expr->lhs && expr->lhs->kind == ExprKind::kMemberAccess;
}

// The arguments of a scope randomize call. Footnote 43 (§A.8.2) bars `null`;
// and the list is a variable_identifier_list, so an argument that is not a
// variable identifier is rejected -- under §G.5, which gives std::randomize
// that form, for a call written through the std package, where the parser
// has already refused every such argument, and under §A.8.2, whose
// randomize_call gives the bare scope form the same list, for a member
// access or a select the parser lets through as a property name of §18.11.
void CheckScopeRandomizeArguments(const Expr* expr, DiagEngine& diag) {
  for (const auto* arg : expr->args) {
    if (!arg) continue;
    if (arg->kind == ExprKind::kIdentifier && arg->text == "null") {
      diag.Error(arg->range.start,
                 "'null' is not a legal argument to a scope randomize call",
                 Subclause("A.8.2"));
    } else if (arg->kind != ExprKind::kIdentifier) {
      const bool kStd = IsStdQualifiedRandomizeCall(expr);
      diag.Error(arg->range.start,
                 kStd ? "argument to std::randomize shall be a variable "
                        "identifier"
                      : "argument to a scope randomize call shall be a "
                        "variable identifier",
                 Subclause(kStd ? "G.5" : "A.8.2"));
    }
  }
}

// Footnote 43 (§A.8.2): in a scope randomize_call, `null` is not a legal
// argument and the with-clause's parenthesized identifier_list is also
// illegal, and §G.5 has the arguments be variable identifiers. Walks the
// expression tree and reports each offending site. The parenthesized-form
// check uses the `with_has_parens` AST flag set by the parser regardless of
// whether the parenthesized list happened to be empty or non-empty.
void CheckScopeRandomizeRulesInExpr(const Expr* expr, DiagEngine& diag) {
  if (!expr) return;
  if (IsScopeRandomizeCall(expr)) {
    CheckScopeRandomizeArguments(expr, diag);
    if (expr->with_has_parens) {
      diag.Error(expr->range.start,
                 "scope randomize call cannot use a parenthesized identifier "
                 "list after 'with'",
                 Subclause("A.8.2"));
    }
  }
  CheckScopeRandomizeRulesInExpr(expr->lhs, diag);
  CheckScopeRandomizeRulesInExpr(expr->rhs, diag);
  CheckScopeRandomizeRulesInExpr(expr->condition, diag);
  CheckScopeRandomizeRulesInExpr(expr->true_expr, diag);
  CheckScopeRandomizeRulesInExpr(expr->false_expr, diag);
  CheckScopeRandomizeRulesInExpr(expr->base, diag);
  CheckScopeRandomizeRulesInExpr(expr->index, diag);
  CheckScopeRandomizeRulesInExpr(expr->index_end, diag);
  for (const auto* a : expr->args) CheckScopeRandomizeRulesInExpr(a, diag);
  for (const auto* e : expr->elements) CheckScopeRandomizeRulesInExpr(e, diag);
}

// Footnote 43 of A.8.2 bars `null` and a parenthesized identifier list from a
// scope randomize_call wherever the call is written, and A.6.4 makes a
// subroutine_call_statement a statement_item, so every position a statement
// holds a statement in is one this walk is owed at. ForEachChildStmt in
// elaborator_validate_internal.h states those positions once for the whole
// elaborator, which is why the list is not written out again here.
void WalkStmtForScopeRandomize(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  CheckScopeRandomizeRulesInExpr(s->expr, diag);
  CheckScopeRandomizeRulesInExpr(s->lhs, diag);
  CheckScopeRandomizeRulesInExpr(s->rhs, diag);
  CheckScopeRandomizeRulesInExpr(s->condition, diag);
  CheckScopeRandomizeRulesInExpr(s->for_cond, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtForScopeRandomize(sub, diag); });
}

// Builds a name→decl map of all callable subroutines (the elaborator's known
// functions plus the task declarations local to `decl`).
// Footnote 43 (§A.8.2): walk every procedural and subroutine body for illegal
// scope randomize_call forms.
void ValidateScopeRandomizeInDecl(const ModuleDecl* decl, DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtForScopeRandomize(item->body, diag);
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (const auto* s : item->func_body_stmts)
        WalkStmtForScopeRandomize(s, diag);
    }
  }
}

}  // namespace

void Elaborator::ValidateScopeRandomizeCalls(const ModuleDecl* decl) {
  ValidateScopeRandomizeInDecl(decl, diag_);
}

}  // namespace delta
