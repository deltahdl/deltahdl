// Annex D.3: "Use of this function is limited, however, it may only be used in
// a continuous assignment statement where the left-hand side is a
// concatenation of scalar nets and the argument to the system function is a
// memory element reference." The function reads one word of a memory and
// drives it onto the scalar nets the concatenation names, one bit each, so
// the three limits are what make the call mean anything: a procedural
// statement has no nets to drive, an expression around the call would take
// the word for a number, and an argument that is no memory element names no
// pattern. Each breach is reported under D.3 at the call.

#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"

namespace delta {

namespace {

constexpr std::string_view kGetpatternLimit =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets";

bool IsGetpatternCall(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kSystemCall &&
         e->callee == "$getpattern";
}

// Reports every $getpattern call at or under `e` as one written where
// `where` says, which is anywhere but as the whole right-hand side of a
// continuous assignment.
void ReportGetpatternUnder(const Expr* e, std::string_view where,
                           DiagEngine& diag) {
  if (e == nullptr) return;
  if (IsGetpatternCall(e)) {
    diag.Error(e->range.start, std::format("{}; {}", kGetpatternLimit, where),
               Subclause("D.3"));
  }
  ForEachExprChild(
      e, [&](const Expr* child) { ReportGetpatternUnder(child, where, diag); });
}

void WalkStmtsForGetpattern(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&](const Expr* e) {
    ReportGetpatternUnder(e, "it is written in a procedural statement", diag);
  });
  ForEachChildStmt(
      s, [&diag](Stmt* const& sub) { WalkStmtsForGetpattern(sub, diag); });
}

}  // namespace

// The placements D.3 excludes: a procedural statement, and an expression of a
// continuous assignment's right-hand side other than the call itself. The
// right-hand side that is the call is validated against its left-hand side
// and its argument by ValidateGetpatternContAssign when the assignment is
// elaborated, where the nets' widths are known.
void Elaborator::ValidateGetpatternUses(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind) && item->body != nullptr) {
      WalkStmtsForGetpattern(item->body, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign &&
        !IsGetpatternCall(item->assign_rhs)) {
      ReportGetpatternUnder(item->assign_rhs,
                            "it is written inside an expression rather than "
                            "as the whole right-hand side",
                            diag_);
    }
  }
}

// Whether `arg` is a memory element reference: a select whose base names a
// variable declared with an unpacked dimension.
bool Elaborator::NamesMemoryElement(const Expr* arg) const {
  if (arg == nullptr || arg->kind != ExprKind::kSelect ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto info = var_array_info_.find(arg->base->text);
  return info != var_array_info_.end() && info->second.num_unpacked_dims > 0;
}

// A continuous assignment whose right-hand side is the call: the left-hand
// side is a concatenation of scalar nets, each element an identifier naming a
// net one bit wide, and the argument is a select of a variable declared with
// an unpacked dimension, which is what a memory element reference is.
void Elaborator::ValidateGetpatternContAssign(const ModuleItem* item,
                                              const RtlirModule* mod) {
  const Expr* call = item->assign_rhs;
  if (!IsGetpatternCall(call)) return;
  const Expr* lhs = item->assign_lhs;
  if (lhs == nullptr || lhs->kind != ExprKind::kConcatenation) {
    diag_.Error(call->range.start,
                std::format("{}; the left-hand side is no concatenation",
                            kGetpatternLimit),
                Subclause("D.3"));
    return;
  }
  for (const auto* el : lhs->elements) {
    bool scalar_net = el->kind == ExprKind::kIdentifier &&
                      net_names_.count(el->text) != 0 &&
                      LookupLhsWidth(el, mod) == 1;
    if (!scalar_net) {
      diag_.Error(el->range.start,
                  std::format("{}; this element of the left-hand side is no "
                              "scalar net",
                              kGetpatternLimit),
                  Subclause("D.3"));
    }
  }
  const Expr* arg = call->args.empty() ? nullptr : call->args[0];
  if (!NamesMemoryElement(arg)) {
    diag_.Error(arg != nullptr ? arg->range.start : call->range.start,
                "$getpattern takes a memory element reference as its "
                "argument, a select of a variable declared with an unpacked "
                "dimension",
                Subclause("D.3"));
  }
}

}  // namespace delta
