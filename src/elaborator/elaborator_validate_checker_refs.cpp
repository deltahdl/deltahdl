#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

static bool ExprRefersToChecker(
    const Expr* e, const std::unordered_set<std::string_view>& checker_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && checker_names.count(leftmost)) return true;
  }
  if (ExprRefersToChecker(e->lhs, checker_names)) return true;
  if (ExprRefersToChecker(e->rhs, checker_names)) return true;
  if (ExprRefersToChecker(e->base, checker_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToChecker(elem, checker_names)) return true;
  }
  return false;
}

static void WalkStmtsForCheckerRef(
    const Stmt* s, std::unordered_set<std::string_view> checker_names,
    DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl)
      checker_names.erase(sub->var_name);
  });
  if (s->lhs && ExprRefersToChecker(s->lhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted",
               Subclause("23.6"));
  if (s->rhs && ExprRefersToChecker(s->rhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted",
               Subclause("23.6"));
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForCheckerRef(sub, checker_names, diag);
  });
}

static void ReportIfRefersToChecker(
    const Expr* e, SourceLoc loc,
    const std::unordered_set<std::string_view>& checker_names,
    DiagEngine& diag) {
  if (ExprRefersToChecker(e, checker_names))
    diag.Error(loc, "hierarchical reference into a checker is not permitted",
               Subclause("23.6"));
}

void Elaborator::ValidateHierRefIntoChecker(const ModuleDecl* decl) {
  if (checker_inst_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ReportIfRefersToChecker(item->assign_lhs, item->loc, checker_inst_names_,
                              diag_);
      ReportIfRefersToChecker(item->assign_rhs, item->loc, checker_inst_names_,
                              diag_);
    }
    if (item->kind == ModuleItemKind::kNetDecl ||
        item->kind == ModuleItemKind::kVarDecl) {
      ReportIfRefersToChecker(item->init_expr, item->loc, checker_inst_names_,
                              diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtsForCheckerRef(item->body, checker_inst_names_, diag_);
  }
}

static void WalkStmtsForFreeBlockingAssign(
    const Stmt* s, std::unordered_set<std::string_view> free_vars,
    DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl)
      free_vars.erase(sub->var_name);
  });
  if (s->kind == StmtKind::kBlockingAssign && s->lhs) {
    auto target = HierRefLeftmost(s->lhs);
    if (!target.empty() && free_vars.count(target))
      diag.Error(
          s->range.start,
          std::format("a blocking assignment cannot target free checker "
                      "variable '{}'; a free variable is updated only by "
                      "a nonblocking assignment",
                      target),
          Subclause("17.7.1"));
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForFreeBlockingAssign(sub, free_vars, diag);
  });
}

static void CheckContAssignNotFreeVariable(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& free_vars, DiagEngine& diag) {
  auto target = HierRefLeftmost(item->assign_lhs);
  if (target.empty() || free_vars.count(target) == 0) return;
  diag.Error(item->loc,
             std::format("a continuous assignment cannot target free checker "
                         "variable '{}'; a free variable is updated only by a "
                         "nonblocking assignment",
                         target),
             Subclause("17.7.1"));
}

void Elaborator::ValidateFreeCheckerVariableAssignments(
    const ModuleDecl* decl) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  std::unordered_set<std::string_view> free_vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->is_rand &&
        !item->name.empty())
      free_vars.insert(item->name);
  }
  if (free_vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      CheckContAssignNotFreeVariable(item, free_vars, diag_);
    if (IsProceduralItemKind(item->kind) && item->body)
      WalkStmtsForFreeBlockingAssign(item->body, free_vars, diag_);
  }
}

static void WalkStmtsForCheckerVarAssignInInitial(
    const Stmt* s, const std::unordered_set<std::string_view>& checker_vars,
    DiagEngine& diag) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs) {
    auto target = HierRefLeftmost(s->lhs);
    if (!target.empty() && checker_vars.count(target))
      diag.Error(s->range.start,
                 std::format("checker variable '{}' cannot be assigned in an "
                             "initial procedure; initialize it in its "
                             "declaration instead",
                             target),
                 Subclause("17.7.1"));
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForCheckerVarAssignInInitial(sub, checker_vars, diag);
  });
}

void Elaborator::ValidateCheckerVariableInitialAssignment(
    const ModuleDecl* decl) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  std::unordered_set<std::string_view> checker_vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      checker_vars.insert(item->name);
  }
  if (checker_vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock && item->body)
      WalkStmtsForCheckerVarAssignInInitial(item->body, checker_vars, diag_);
  }
}

}  // namespace delta
