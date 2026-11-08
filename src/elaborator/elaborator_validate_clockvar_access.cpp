#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

template <typename ClockingSignalMap>
void CheckClockvarMemberAccessDirection(
    const Expr* e, bool is_lvalue, const ClockingSignalMap& clocking_signals,
    DiagEngine& diag) {
  if (e->kind != ExprKind::kMemberAccess || !e->lhs ||
      e->lhs->kind != ExprKind::kIdentifier) {
    return;
  }
  auto block_it = clocking_signals.find(e->lhs->text);
  if (block_it == clocking_signals.end()) return;
  std::string_view member;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
    member = e->rhs->text;
  } else if (!e->text.empty()) {
    member = e->text;
  }
  if (member.empty()) return;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return;
  if (is_lvalue && sig_it->second.direction == Direction::kInput) {
    diag.Error(
        e->range.start,
        std::format("write to input clockvar '{}.{}'", e->lhs->text, member),
        Subclause("14.3"));
  }
  if (!is_lvalue && sig_it->second.direction == Direction::kOutput) {
    diag.Error(
        e->range.start,
        std::format("read from output clockvar '{}.{}'", e->lhs->text, member),
        Subclause("14.3"));
  }
}

}  // namespace

void Elaborator::CheckClockvarAccessExpr(const Expr* e, bool is_lvalue) {
  if (!e) return;
  CheckClockvarMemberAccessDirection(e, is_lvalue, clocking_signals_, diag_);
  if (!is_lvalue) {
    ForEachExprChild(
        e, [this](const Expr* sub) { CheckClockvarAccessExpr(sub, false); });
    return;
  }
  if (e->kind == ExprKind::kSelect) {
    CheckClockvarAccessExpr(e->base, true);
    CheckClockvarAccessExpr(e->index, false);
    CheckClockvarAccessExpr(e->index_end, false);
    return;
  }
  for (const Expr* elem : e->elements) CheckClockvarAccessExpr(elem, true);
}

void Elaborator::WalkStmtsForClockvarAccess(const Stmt* s) {
  if (!s) return;
  CheckClockvarAccessExpr(s->lhs, true);
  ForEachChildExpr(s, [this, s](const Expr* e) {
    if (e != s->lhs) CheckClockvarAccessExpr(e, false);
  });
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForClockvarAccess(sub); });
}

void Elaborator::ValidateClockvarAccess(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  for (const auto& root : roots) WalkStmtsForClockvarAccess(root.body);
}

}  // namespace delta
