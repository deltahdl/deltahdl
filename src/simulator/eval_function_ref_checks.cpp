#include <string>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"

namespace delta {

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  bool is_static = func->is_static && !func->is_automatic;
  if (!is_static) return;
  for (const auto& arg : func->func_args) {
    // §13.5.2: pass-by-reference is illegal in a static-lifetime subroutine,
    // except for a `ref static` argument, which is explicitly permitted.
    if (arg.direction == Direction::kRef && !arg.is_ref_static) {
      diag.Error(func->loc,
                 "ref argument '" + std::string(arg.name) +
                     "' not allowed in static subroutine '" +
                     std::string(func->name) + "'",
                 Subclause("13.5.2"));
    }
  }
}

static std::string_view GetLhsRootName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect && e->base) return GetLhsRootName(e->base);
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return GetLhsRootName(e->lhs);
  return {};
}

static void CheckConstRefWrites(
    const Stmt* stmt,
    const std::unordered_set<std::string_view>& const_ref_names,
    const ModuleItem* func, DiagEngine& diag) {
  if (!stmt) return;
  switch (stmt->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kForce: {
      auto root = GetLhsRootName(stmt->lhs);
      if (!root.empty() && const_ref_names.count(root)) {
        diag.Error(stmt->range.start,
                   "cannot write to const ref argument '" + std::string(root) +
                       "' in subroutine '" + std::string(func->name) + "'",
                   Subclause("13.5.2"));
      }
      break;
    }
    default:
      break;
  }
  for (auto* s : stmt->stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->then_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->else_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->body, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->for_body, const_ref_names, func, diag);
  for (auto* s : stmt->for_inits)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (auto* s : stmt->for_steps)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (const auto& ci : stmt->case_items)
    CheckConstRefWrites(ci.body, const_ref_names, func, diag);
  for (auto* s : stmt->fork_stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_pass_stmt, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_fail_stmt, const_ref_names, func, diag);
  for (const auto& ri : stmt->randcase_items)
    CheckConstRefWrites(ri.second, const_ref_names, func, diag);
}

void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  std::unordered_set<std::string_view> const_ref_names;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kRef && arg.is_const) {
      const_ref_names.insert(arg.name);
    }
  }
  if (const_ref_names.empty()) return;
  for (auto* stmt : func->func_body_stmts) {
    CheckConstRefWrites(stmt, const_ref_names, func, diag);
  }
}

}  // namespace delta
