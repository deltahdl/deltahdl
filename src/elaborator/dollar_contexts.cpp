#include "elaborator/dollar_contexts.h"

#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/declared_types.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
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

bool IsLoneDollar(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

bool ContainsDollar(const Expr* e) {
  if (e == nullptr) return false;
  if (IsLoneDollar(e)) return true;
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
  const std::unordered_set<std::string_view>& dollar_takers;
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

static void AddDollarTakerNames(const std::vector<ModuleItem*>& items,
                                std::unordered_set<std::string_view>& names) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kSequenceDecl ||
        item->kind == ModuleItemKind::kPropertyDecl) {
      names.insert(item->name);
    }
    const ModuleDecl* nested = item->nested_module_decl;
    if (nested != nullptr && nested->decl_kind == ModuleDeclKind::kChecker)
      names.insert(nested->name);
  }
}

static std::unordered_set<std::string_view> DollarTakers(
    const ModuleDecl* decl, const CompilationUnit& unit) {
  std::unordered_set<std::string_view> names;
  AddDollarTakerNames(decl->items, names);
  AddDollarTakerNames(unit.cu_items, names);
  for (const PackageDecl* pkg : unit.packages)
    AddDollarTakerNames(pkg->items, names);
  for (const ModuleDecl* checker : unit.checkers) names.insert(checker->name);
  return names;
}

static bool SelectsANonQueue(const Expr* select, const DollarScan& scan) {
  const Expr* base = select->base;
  return base != nullptr && base->kind == ExprKind::kIdentifier &&
         scan.non_queues.count(base->text) != 0;
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan);

static void CheckRangeBound(const Expr* bound, const DollarScan& scan) {
  if (bound != nullptr && IsLoneDollar(bound)) return;
  CheckDollarOperand(bound, scan);
}

static bool IsToleranceRange(const Expr* range) {
  return range->op == TokenKind::kPlusSlashMinus ||
         range->op == TokenKind::kPlusPercentMinus;
}

static void CheckSelect(const Expr* e, const DollarScan& scan) {
  if (e->base == nullptr && !IsToleranceRange(e)) {
    CheckRangeBound(e->index, scan);
    CheckRangeBound(e->index_end, scan);
    return;
  }
  CheckDollarOperand(e->base, scan);
  if (e->base == nullptr || SelectsANonQueue(e, scan)) {
    CheckDollarOperand(e->index, scan);
    CheckDollarOperand(e->index_end, scan);
  }
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan) {
  if (e == nullptr) return;
  if (IsQueueDim(e)) {
    ReportDollar(e, scan.diag);
    return;
  }
  if (e->kind == ExprKind::kSelect) {
    CheckSelect(e, scan);
    return;
  }
  if (e->kind == ExprKind::kCall && scan.dollar_takers.count(e->callee) != 0)
    return;
  ForEachExprChild(
      e, [&scan](const Expr* child) { CheckDollarOperand(child, scan); });
}

static void CheckUnpackedDims(const std::vector<Expr*>& dims,
                              const DollarScan& scan) {
  for (const Expr* dim : dims) {
    CheckDollarOperand(IsQueueDim(dim) ? dim->rhs : dim, scan);
  }
}

static void CheckDeclaredDims(const DataType& type,
                              const std::vector<Expr*>& unpacked_dims,
                              const DollarScan& scan) {
  CheckDollarOperand(type.packed_dim_left, scan);
  CheckDollarOperand(type.packed_dim_right, scan);
  for (const auto& [left, right] : type.extra_packed_dims) {
    CheckDollarOperand(left, scan);
    CheckDollarOperand(right, scan);
  }
  CheckUnpackedDims(unpacked_dims, scan);
}

static void CheckDollarStmt(const Stmt* s, const DollarScan& scan) {
  if (s == nullptr) return;
  const std::vector<Expr*>& dims = s->var_unpacked_dims;
  ForEachChildExpr(s, [&scan, &dims](const Expr* e) {
    if (std::ranges::find(dims, e) == dims.end()) CheckDollarOperand(e, scan);
  });
  ForEachChildStmt(s,
                   [&scan](Stmt* const& sub) { CheckDollarStmt(sub, scan); });
}

static void CheckInstanceActuals(const ModuleItem* item,
                                 const DollarScan& scan) {
  if (scan.dollar_takers.count(item->inst_module) != 0) return;
  for (const auto& [name, actual] : item->inst_ports)
    CheckDollarOperand(actual, scan);
}

static void CheckDollarItem(const ModuleItem* item, const DollarScan& scan) {
  switch (item->kind) {
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kNetDecl:
      CheckDollarOperand(item->init_expr, scan);
      CheckDeclaredDims(item->data_type, item->unpacked_dims, scan);
      break;
    case ModuleItemKind::kTypedef:
      CheckDeclaredDims(item->typedef_type, item->unpacked_dims, scan);
      break;
    case ModuleItemKind::kModuleInst:
      CheckInstanceActuals(item, scan);
      break;
    default:
      for (const auto& [target, value] : item->defparam_assigns)
        CheckDollarOperand(value, scan);
      break;
  }
  CheckDollarOperand(item->assign_lhs, scan);
  CheckDollarOperand(item->assign_rhs, scan);
  CheckDollarStmt(item->body, scan);
  for (const Stmt* s : item->func_body_stmts) CheckDollarStmt(s, scan);
}

void CheckDollarOperands(const ModuleDecl* decl, const CompilationUnit& unit,
                         DiagEngine& diag) {
  const std::unordered_set<std::string_view> kNonQueues = NonQueueNames(decl);
  const std::unordered_set<std::string_view> kTakers = DollarTakers(decl, unit);
  const DollarScan kScan{kNonQueues, kTakers, diag};
  for (const ModuleItem* item : decl->items) CheckDollarItem(item, kScan);
  ForEachInnerDeclaredType(decl, [&kScan](const DeclaredType& declared) {
    CheckDeclaredDims(declared.type, declared.unpacked_dims, kScan);
  });
}

}  // namespace delta
