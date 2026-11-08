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
  if (s->kind == StmtKind::kExprStmt) {
    ReportConstMutatingMethodCall(s->expr, s->range.start);
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kForce ||
      s->kind == StmtKind::kAssign) {
    ReportConstantRootedTarget(s->lhs, s, const_names_, enum_member_names_,
                               diag_);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkStmtsForConstAssign(sub); });
}

void Elaborator::ValidateConstAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) WalkStmtsForConstAssign(item->body);
    for (const auto* sub : item->func_body_stmts) WalkStmtsForConstAssign(sub);
  }
}
}  // namespace delta
