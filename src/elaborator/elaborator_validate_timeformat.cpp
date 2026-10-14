// §20.4.3: Syntax 20-5 gives $timeformat no argument list or all four of its
// arguments.

#include <algorithm>
#include <cstddef>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// Syntax 20-5's argument list: units_number, precision_number, suffix_string
// and minimum_field_width.
constexpr size_t kTimeformatArgs = 4;

// The list is optional as a whole, but each of its four arguments is required:
// an empty `()` and an empty position, which the parser keeps as a null
// argument, match neither form.
bool IsTimeformatArgListValid(const Expr* call) {
  if (!call->has_arg_list) return true;
  if (call->args.size() != kTimeformatArgs) return false;
  return std::ranges::none_of(call->args,
                              [](const Expr* a) { return a == nullptr; });
}

void CheckTimeformatExpr(const Expr* e, DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$timeformat" &&
      !IsTimeformatArgListValid(e)) {
    diag.Error(e->range.start,
               "'$timeformat' takes all four of its arguments or none",
               Subclause("20.4.3"));
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckTimeformatExpr(child, diag); });
}

// §20.4.3 names no position the call may stand in, so every expression of
// every statement is one the check is owed at.
void CheckTimeformatStmt(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&](const Expr* e) { CheckTimeformatExpr(e, diag); });
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CheckTimeformatStmt(sub, diag); });
}

}  // namespace

void CheckTimeformatArgs(const ModuleDecl* decl, DiagEngine& diag) {
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  for (const auto& root : roots) CheckTimeformatStmt(root.body, diag);
}

}  // namespace delta
