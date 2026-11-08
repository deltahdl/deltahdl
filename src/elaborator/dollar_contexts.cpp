#include "elaborator/dollar_contexts.h"

#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool AnyScalarChildContainsDollar(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,        e->rhs,          e->condition,   e->true_expr,
      e->false_expr, e->base,         e->index,       e->index_end,
      e->with_expr,  e->stream_range, e->repeat_count};
  for (const Expr* c : kChildren) {
    if (ContainsDollar(c)) return true;
  }
  return false;
}

}  // namespace

bool ContainsDollar(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "$") return true;
  if (AnyScalarChildContainsDollar(e)) return true;
  for (const Expr* a : e->args)
    if (ContainsDollar(a)) return true;
  for (const Expr* el : e->elements)
    if (ContainsDollar(el)) return true;
  return false;
}

namespace {

struct QueueContextScan {
  const std::unordered_set<std::string_view>& unbounded;
  const std::unordered_set<std::string_view>& queues;
  DiagEngine& diag;
};

}  // namespace

static bool NamesUnboundedParam(const Expr* e, const QueueContextScan& scan) {
  return e->kind == ExprKind::kIdentifier && e->scope_prefix.empty() &&
         scan.unbounded.count(e->text) != 0;
}

static void Report(const Expr* param, const QueueContextScan& scan) {
  scan.diag.Error(param->range.start,
                  std::format("parameter '{}' holds '$', which a queue context "
                              "does not permit",
                              param->text),
                  Subclause("6.20.7"));
}

static void ReportUnboundedParamsIn(const Expr* e,
                                    const QueueContextScan& scan) {
  if (e == nullptr) return;
  if (NamesUnboundedParam(e, scan)) Report(e, scan);
  ForEachExprChild(
      e, [&scan](const Expr* child) { ReportUnboundedParamsIn(child, scan); });
}

static void CheckDims(const std::vector<Expr*>& dims,
                      const QueueContextScan& scan) {
  for (const Expr* dim : dims) {
    if (IsQueueDim(dim)) {
      ReportUnboundedParamsIn(dim->rhs, scan);
    } else if (dim != nullptr && NamesUnboundedParam(dim, scan)) {
      Report(dim, scan);
    }
  }
}

static void CheckExpr(const Expr* e, const QueueContextScan& scan) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      e->base->kind == ExprKind::kIdentifier &&
      scan.queues.count(e->base->text) != 0) {
    ReportUnboundedParamsIn(e->index, scan);
    ReportUnboundedParamsIn(e->index_end, scan);
  }
  ForEachExprChild(e, [&scan](const Expr* child) { CheckExpr(child, scan); });
}

static void CheckStmt(const Stmt* s, const QueueContextScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) CheckDims(s->var_unpacked_dims, scan);
  ForEachChildExpr(s, [&scan](const Expr* e) { CheckExpr(e, scan); });
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { CheckStmt(sub, scan); });
}

void CheckUnboundedParamsInQueueContexts(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& unbounded,
    const std::unordered_set<std::string_view>& queues, DiagEngine& diag) {
  if (unbounded.empty()) return;
  const QueueContextScan kScan{unbounded, queues, diag};
  for (const ModuleItem* item : decl->items) {
    CheckDims(item->unpacked_dims, kScan);
    CheckExpr(item->init_expr, kScan);
    CheckExpr(item->assign_lhs, kScan);
    CheckExpr(item->assign_rhs, kScan);
    CheckStmt(item->body, kScan);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, kScan);
  }
}

static void ReportDollar(const Expr* e, DiagEngine& diag) {
  diag.Error(e->range.start,
             "'$' may stand only in a queue's dimension or select, a value "
             "range's bound, a cycle delay range's bound, a sequence, "
             "property or checker argument, or a parameter's value",
             Subclause("6.20.7"));
}

namespace {

struct DollarScan {
  const std::unordered_set<std::string_view>& non_queues;
  DiagEngine& diag;
};

}  // namespace

static std::unordered_set<std::string_view> NonQueueNames(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> names;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    const std::vector<Expr*>& dims = item->unpacked_dims;
    bool fixed_first = !dims.empty() && !IsQueueDim(dims[0]);
    bool plain = dims.empty() && item->data_type.kind != DataTypeKind::kNamed &&
                 item->data_type.type_ref_expr == nullptr;
    if (fixed_first || plain) names.insert(item->name);
  }
  return names;
}

static bool SelectsANonQueue(const Expr* select, const DollarScan& scan) {
  const Expr* base = select->base;
  return base != nullptr && base->kind == ExprKind::kIdentifier &&
         scan.non_queues.count(base->text) != 0;
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan) {
  if (e == nullptr) return;
  if (IsQueueDim(e)) {
    ReportDollar(e, scan.diag);
    return;
  }
  if (e->kind == ExprKind::kSelect) {
    CheckDollarOperand(e->base, scan);
    if (SelectsANonQueue(e, scan)) {
      CheckDollarOperand(e->index, scan);
      CheckDollarOperand(e->index_end, scan);
    }
    return;
  }
  if (e->kind == ExprKind::kCall) return;
  ForEachExprChild(
      e, [&scan](const Expr* child) { CheckDollarOperand(child, scan); });
}

static void CheckDollarStmt(const Stmt* s, const DollarScan& scan) {
  if (s == nullptr) return;
  const Expr* const kOperands[] = {s->lhs,       s->rhs,      s->expr,
                                   s->condition, s->var_init, s->for_cond};
  for (const Expr* e : kOperands) CheckDollarOperand(e, scan);
  ForEachChildStmt(s,
                   [&scan](Stmt* const& sub) { CheckDollarStmt(sub, scan); });
}

void CheckDollarOperands(const ModuleDecl* decl, DiagEngine& diag) {
  const std::unordered_set<std::string_view> kNonQueues = NonQueueNames(decl);
  const DollarScan kScan{kNonQueues, diag};
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      CheckDollarOperand(item->init_expr, kScan);
    }
    CheckDollarOperand(item->assign_lhs, kScan);
    CheckDollarOperand(item->assign_rhs, kScan);
    CheckDollarStmt(item->body, kScan);
    for (const Stmt* s : item->func_body_stmts) CheckDollarStmt(s, kScan);
  }
}

}  // namespace delta
