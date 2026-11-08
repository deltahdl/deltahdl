#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

constexpr std::string_view kGetpatternLimit =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets";

bool IsGetpatternCall(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kSystemCall &&
         e->callee == "$getpattern";
}

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

bool Elaborator::NamesMemoryElement(const Expr* arg) const {
  if (arg == nullptr || arg->kind != ExprKind::kSelect ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto info = var_array_info_.find(arg->base->text);
  return info != var_array_info_.end() && info->second.num_unpacked_dims > 0;
}

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
