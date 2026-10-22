// §6.20: the rule that a constant never changes, enforced over every procedural
// write that could break it.
// A constant is a named data object that never changes, and parameter,
// localparam and specparam are the three elaboration-time constants (§6.20).
// Elaborator::const_names_ holds all three, so one walk answers for all three,
// and the two questions asked of a statement are whether an assignment's
// left-hand side reaches one of those names and whether a call statement writes
// one through a method that writes its object.
//
// These are here rather than in src/elaborator/elaborator_validate_types.cpp,
// where they stood, because that file reached the 1000-line maximum
// assert-no-oversized-source-files in .github/workflows/deltahdl.yml fails at.
// §6.20 is a rule of its own and its checks call nothing else in that file.
//
// §10.4 and §10.6 bound what a procedural assignment and a procedural
// continuous assignment write, and a constant is outside every one of those
// bounds, so the same walk asks of each such statement whether its target is
// rooted at one -- of a blocking or nonblocking assignment, whether at a name
// an enumeration declares, since §6.20 already answers for a parameter
// constant.

#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/string_methods.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// The name a left-hand side writes through, or nullptr where it writes through
// no single name. §11.5.1's bit-select and part-select and §7.2's member access
// each select part of a named object and store into that object, so the object
// written is the identifier underneath them however many of them are stacked
// up. Whether the write is legal turns on what that name is, not on how much of
// it the write reaches.
static const Expr* LvalueBaseIdentifier(const Expr* e) {
  while (e != nullptr && e->base != nullptr &&
         (e->kind == ExprKind::kSelect ||
          (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution))) {
    e = e->base;
  }
  return (e != nullptr && e->kind == ExprKind::kIdentifier) ? e : nullptr;
}

void Elaborator::ReportConstAssignTarget(const Expr* lhs, SourceLoc loc) {
  if (lhs == nullptr) return;
  // §11.4.12 makes a concatenation a legal left-hand side, and every operand of
  // one is written, so each is asked about in turn rather than the
  // concatenation as a whole being passed over for having no name of its own.
  if (lhs->kind == ExprKind::kConcatenation ||
      lhs->kind == ExprKind::kReplicate ||
      lhs->kind == ExprKind::kStreamingConcat) {
    for (const Expr* element : lhs->elements) {
      ReportConstAssignTarget(element, loc);
    }
    return;
  }
  const Expr* base = LvalueBaseIdentifier(lhs);
  if (base == nullptr || const_names_.count(base->text) == 0) return;
  diag_.Error(loc, std::format("assignment to constant '{}'", base->text),
              Subclause("6.20"));
}

// §10.4.1 and §10.4.2 write the target of a blocking and a nonblocking
// assignment as a variable_lvalue (Syntax 10-2), Syntax 10-4 in §10.6 writes a
// procedural `assign` as a variable_assignment and a `force` as that or a
// net_assignment, and §10.6.1 and §10.6.2 bound those two to variables and, for
// a force, nets. A parameter constant (§6.20) and a name an enumeration
// declares (§6.19) are constants and none of these, so a target rooted at one,
// or an element of a concatenation rooted at one, is reported under the
// subclause bounding the statement `s`. A blocking or nonblocking write to a
// parameter constant is §6.20's report (Elaborator::ReportConstAssignTarget),
// so only an enumeration's name is asked about for those two.
static void ReportConstantRootedTarget(const Expr* lhs, const Stmt* s,
                                       const NameSet& const_names,
                                       const NameSet& enum_members,
                                       DiagEngine& diag) {
  if (lhs->kind == ExprKind::kConcatenation) {
    for (const Expr* element : lhs->elements)
      ReportConstantRootedTarget(element, s, const_names, enum_members, diag);
    return;
  }
  const Expr* base = LvalueBaseIdentifier(lhs);
  if (base == nullptr) return;
  bool continuous = s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign;
  if (enum_members.count(base->text) == 0 &&
      (!continuous || const_names.count(base->text) == 0))
    return;
  std::string_view what = "assignment";
  std::string_view bound;
  std::string_view subclause = "10.4";
  if (s->kind == StmtKind::kForce) {
    what = "force";
    bound = " or a net";
    subclause = "10.6.2";
  } else if (s->kind == StmtKind::kAssign) {
    what = "procedural assign";
    subclause = "10.6.1";
  }
  diag.Error(s->range.start,
             std::format("{} of constant '{}', which is not a variable{}", what,
                         base->text, bound),
             Subclause(subclause));
}

void Elaborator::ReportConstMutatingMethodCall(const Expr* call,
                                               SourceLoc loc) {
  if (call == nullptr || call->kind != ExprKind::kCall) return;
  // §13.5 writes a method call as `expression.method(...)`, which the parser
  // records as a kCall whose callee is the kMemberAccess naming the method. A
  // `::` name is a scoped one and names no object to write.
  const Expr* callee = call->lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess) return;
  if (callee->is_scope_resolution || callee->rhs == nullptr) return;
  if (!StringMethodWritesItsObject(callee->rhs->text)) return;
  ReportConstAssignTarget(callee->lhs, loc);
}

void Elaborator::WalkStmtsForConstAssign(const Stmt* s) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    ReportConstAssignTarget(s->lhs, s->range.start);
  }
  // §6.16 gives six string methods that write the string they are called on, so
  // a call statement writes a constant as surely as an assignment to one does.
  // At run time a parameter is an ordinary Variable with no flag marking it
  // constant, so nothing downstream refuses the write.
  if (s->kind == StmtKind::kExprStmt) {
    ReportConstMutatingMethodCall(s->expr, s->range.start);
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kForce ||
      s->kind == StmtKind::kAssign) {
    ReportConstantRootedTarget(s->lhs, s, const_names_, enum_member_names_,
                               diag_);
  }
  // Every member of Stmt that holds a statement, taken from ForEachChildStmt in
  // elaborator_validate_internal.h rather than listed again here. §6.20 puts no
  // condition on where the write stands, so a statement this walk misses is a
  // place a write to a constant goes unreported, and which member holds a given
  // statement says nothing about whether §6.20 covers it. Keeping the list in
  // one place is what stops this rule and the list from disagreeing about which
  // members those are.
  //
  // The visitor takes `Stmt* const&` because `s` is a `const Stmt*`, which is
  // how ForEachChildStmt lets a walk that only reads the tree share its list
  // with the walks that rewrite it. Nothing here stops early, since §6.20 is
  // broken as many times as a source writes a constant and each write is
  // reported where it stands.
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkStmtsForConstAssign(sub); });
}

void Elaborator::ValidateConstAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) WalkStmtsForConstAssign(item->body);
    // §9.2 counts a task and a function structured procedures as well, and a
    // write to a constant from inside one breaks §6.20 exactly as a write from
    // an initial block does. Neither is one of IsProceduralItemKind's six,
    // because both carry their statements in ModuleItem::func_body_stmts rather
    // than under ModuleItem::body, which is what left them unwalked. The list
    // is empty for every item that is not a subroutine, so no kind test guards
    // it.
    for (const auto* sub : item->func_body_stmts) WalkStmtsForConstAssign(sub);
  }
}
}  // namespace delta
