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

// Reports every `$` parameter written anywhere inside `e`.
static void ReportUnboundedParamsIn(const Expr* e,
                                    const QueueContextScan& scan) {
  if (e == nullptr) return;
  if (NamesUnboundedParam(e, scan)) Report(e, scan);
  ForEachExprChild(
      e, [&scan](const Expr* child) { ReportUnboundedParamsIn(child, scan); });
}

// A queue dimension's bound is a queue context, and so is a dimension written
// as a `$` parameter alone, which stands for `[$]`. A fixed dimension written
// in terms of one is not a queue's, and §6.20.7's other contexts decide it.
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

// §7.10: an index or a slice of a queue is a queue select, the one context
// where `$` itself may carry operators, and the one a `$` parameter may not
// enter. A value range of `inside` is a select with no base, and selects
// nothing.
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

// What the `$` operand check reads: the module's variables known to be no
// queue, and the engine its reports go to.
struct DollarScan {
  const std::unordered_set<std::string_view>& non_queues;
  DiagEngine& diag;
};

}  // namespace

// The module's variables that are no queue whatever their type names: one
// whose declaration writes an unpacked dimension first that is not `[$]`, and
// one written with none whose type is neither a typedef name nor a type
// reference, either of which can stand for a queue (§7.10).
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

// Whether `select` selects from one of the module's variables that is no
// queue, named alone. A value range of `inside` is a select with no base.
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
    // A.10 footnote 47: the `$` primary stands for the last element of a
    // queue, in its select alone, so one in the select of a variable that is
    // no queue is an operand like any other.
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
    // A parameter's value is a context the subclause lists, and a sequence's
    // or property's body holds cycle delay ranges, so a declaration's
    // initializer is read for a variable or a net alone.
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
