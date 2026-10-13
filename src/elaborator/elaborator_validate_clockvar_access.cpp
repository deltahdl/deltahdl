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

// §14.3's direction rules on a clockvar: no write to an input clockvar and no
// read of an output one. Kept apart from elaborator_validate_clocking.cpp,
// which stood near the size the assert-no-oversized-source-files job fails at.

namespace delta {

namespace {

// Report a clockvar direction violation for a member-access expression `e`: a
// write (lvalue) to an input clockvar or a read from an output clockvar.
// (Templated so the private nested info type need not be named here.)
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

// §14.3 states the read rule for an output clockvar wherever the read stands,
// so a read is looked for in every child AnyExprChild names: a select's base
// and index, a call's arguments and the operands of every operator. A write
// position is the target of an assignment. §14.16 lets a drive name a select
// of a clockvar, so the base of a select written to and each element of a
// concatenation written to are write positions too, and an index of a select
// written to is read.
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

// Every statement keeps the target it writes in Stmt::lhs -- an assignment,
// assign, deassign, force and release -- and every other expression it holds
// is read, which ForEachChildExpr in elaborator_validate_internal.h lists: a
// condition, an event control, a case expression, a loop condition and the
// rest. §14.3 names no statement a clockvar access is exempt in, so this
// descends every link ForEachChildStmt names.
void Elaborator::WalkStmtsForClockvarAccess(const Stmt* s) {
  if (!s) return;
  CheckClockvarAccessExpr(s->lhs, true);
  ForEachChildExpr(s, [this, s](const Expr* e) {
    if (e != s->lhs) CheckClockvarAccessExpr(e, false);
  });
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForClockvarAccess(sub); });
}

// §14.3 states the rules for the clockvar, whatever procedural code holds the
// access, so a task or function body and a process in a generate block are
// walked with the module's own processes (CollectProceduralRoots).
void Elaborator::ValidateClockvarAccess(const ModuleDecl* decl) {
  if (clocking_signals_.empty()) return;
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  for (const auto& root : roots) WalkStmtsForClockvarAccess(root.body);
}

}  // namespace delta
