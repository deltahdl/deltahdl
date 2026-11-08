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

constexpr size_t kTimeformatArgs = 4;

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
