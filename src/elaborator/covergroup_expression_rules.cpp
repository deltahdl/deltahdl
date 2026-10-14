#include "elaborator/covergroup_expression_rules.h"

#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/checker_procedure_rules.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using Names = std::unordered_set<std::string_view>;

// A covergroup whose covergroup_expressions are being checked, with what it
// reads where it is declared and where the reports go.
struct ExprSite {
  const CovergroupDecl& cg;
  const CovergroupContext& ctx;
  DiagEngine& diag;
};

// Adds to `reads` the names `s` and the statements it holds read, and to
// `own` the names they declare.
void CollectStmtReads(const Stmt* s, Names& own,
                      std::vector<const Expr*>& reads) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) own.insert(s->var_name);
  ForEachChildExpr(s, [&](const Expr* e) { CollectBareIdents(e, reads); });
  ForEachChildStmt(s,
                   [&](const Stmt* sub) { CollectStmtReads(sub, own, reads); });
}

// §19.5: the restrictions on a function the call `call` makes.
void CheckFunctionCall(const Expr* call, const ExprSite& site) {
  const ModuleItem* fn = site.ctx.function_named(call->callee);
  if (fn == nullptr) return;
  if (HasArgumentWrittenBack(fn)) {
    site.diag.Error(call->range.start,
                    std::format("function '{}' has an output, inout or ref "
                                "argument and cannot be called in a "
                                "covergroup_expression",
                                fn->name),
                    Subclause("19.5"));
  }
  if (FunctionIsImpure(fn)) {
    site.diag.Error(call->range.start,
                    std::format("function '{}' keeps state or has a side "
                                "effect and cannot be called in a "
                                "covergroup_expression",
                                fn->name),
                    Subclause("19.5"));
  }
  std::string_view outside = NonConstantReadOutside(*fn, site.ctx);
  if (outside.empty()) return;
  site.diag.Error(call->range.start,
                  std::format("function '{}' reads '{}', a variable outside "
                              "it that is no constant, and cannot be called in "
                              "a covergroup_expression",
                              fn->name, outside),
                  Subclause("19.5"));
}

// §19.5: the calls `e` and its subexpressions make.
void CheckCalls(const Expr* e, const ExprSite& site) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && !IsConstantSysFunc(e->callee)) {
    site.diag.Error(e->range.start,
                    std::format("system function '{}' is no constant system "
                                "function and cannot be called in a "
                                "covergroup_expression",
                                e->callee),
                    Subclause("19.5"));
  } else if (e->kind == ExprKind::kCall) {
    CheckFunctionCall(e, site);
  }
  ForEachExprChild(e, [&](const Expr* child) { CheckCalls(child, site); });
}

// §19.5: the names `e` reads, `free` holding those it may read whatever they
// are.
void CheckNames(const Expr* e, const Names& free, const ExprSite& site) {
  std::vector<const Expr*> reads;
  CollectBareIdents(e, reads);
  for (const Expr* read : reads) {
    if (free.contains(read->text)) continue;
    if (FindCovergroupFormal(site.cg, read->text) != nullptr) {
      if (!IsRefCovergroupFormal(site.cg, read->text)) continue;
      site.diag.Error(read->range.start,
                      std::format("'{}' is a ref formal of covergroup '{}' and "
                                  "cannot be read in a covergroup_expression",
                                  read->text, site.cg.name),
                      Subclause("19.5"));
    } else if (site.ctx.non_constant(read->text)) {
      site.diag.Error(read->range.start,
                      std::format("'{}' is no constant and cannot be read in a "
                                  "covergroup_expression",
                                  read->text),
                      Subclause("19.5"));
    }
  }
}

// One covergroup_expression, `free` holding the names it may read whatever
// they are.
void CheckExpression(const Expr* e, const Names& free, const ExprSite& site) {
  if (e == nullptr) return;
  CheckNames(e, free, site);
  CheckCalls(e, site);
}

void CheckRanges(const std::vector<CovergroupValueRange>& ranges,
                 const ExprSite& site) {
  for (const CovergroupValueRange& range : ranges) {
    CheckExpression(range.lo, {}, site);
    CheckExpression(range.hi, {}, site);
  }
}

void CheckTransitions(const std::vector<TransSet>& transitions,
                      const ExprSite& site) {
  for (const TransSet& set : transitions) {
    for (const TransRangeList& step : set.steps) {
      CheckRanges(step.items, site);
      CheckExpression(step.repeat_lo, {}, site);
      CheckExpression(step.repeat_hi, {}, site);
    }
  }
}

void CheckCoverpointBins(const CoverPointDecl& cp, const ExprSite& site) {
  const Names kItem{"item"};
  for (const BinsOrOptions& bins : cp.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) continue;
    CheckRanges(bins.ranges, site);
    CheckTransitions(bins.transitions, site);
    CheckExpression(bins.array_size, {}, site);
    CheckExpression(bins.with_expr, kItem, site);
  }
}

// §19.6: the covergroup_expressions of the select expression `s` of a cross
// whose items are `items`.
void CheckSelect(const SelectExpression* s, const Names& items,
                 const ExprSite& site) {
  if (s == nullptr) return;
  CheckRanges(s->intersect, site);
  if (s->kind == SelectExpressionKind::kWith) {
    CheckExpression(s->expr, items, site);
  }
  CheckExpression(s->matches, {}, site);
  CheckSelect(s->lhs, items, site);
  CheckSelect(s->rhs, items, site);
}

void CheckCrossBins(const CoverCrossDecl& cross, const ExprSite& site) {
  Names items;
  for (const CrossItem& item : cross.items) items.insert(item.name);
  for (const CrossBodyItem& body : cross.body) {
    if (body.kind == CrossBodyItemKind::kBinsSelection) {
      CheckSelect(body.bins.select, items, site);
    }
  }
}

}  // namespace

std::string_view NonConstantReadOutside(const ModuleItem& fn,
                                        const CovergroupContext& ctx) {
  Names own{fn.name};
  for (const FunctionArg& arg : fn.func_args) own.insert(arg.name);
  std::vector<const Expr*> reads;
  for (const Stmt* s : fn.func_body_stmts) CollectStmtReads(s, own, reads);
  for (const Expr* read : reads) {
    if (!own.contains(read->text) && ctx.non_constant(read->text)) {
      return read->text;
    }
  }
  return {};
}

void CheckCovergroupExpressions(const CovergroupDecl& cg,
                                const CovergroupContext& ctx,
                                DiagEngine& diag) {
  const ExprSite kSite{cg, ctx, diag};
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kCoverPoint) {
      CheckCoverpointBins(*item.cover_point, kSite);
    } else if (item.kind == CoverageSpecKind::kCoverCross) {
      CheckCrossBins(*item.cover_cross, kSite);
    }
  }
}

}  // namespace delta
