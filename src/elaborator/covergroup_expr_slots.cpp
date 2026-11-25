#include "elaborator/covergroup_expr_slots.h"

#include <vector>

#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

void ForEachRangeExpr(const std::vector<CovergroupValueRange>& ranges,
                      const CovergroupExprVisitor& fn) {
  for (const CovergroupValueRange& range : ranges) {
    fn(range.lo);
    fn(range.hi);
  }
}

void ForEachBinsExpr(const BinsOrOptions& bins,
                     const CovergroupExprVisitor& fn) {
  for (const Expr* e : {bins.option.value, bins.array_size, bins.with_expr,
                        bins.set_expr, bins.iff}) {
    fn(e);
  }
  ForEachRangeExpr(bins.ranges, fn);
  for (const TransSet& set : bins.transitions) {
    for (const TransRangeList& step : set.steps) {
      ForEachRangeExpr(step.items, fn);
      fn(step.repeat_lo);
      fn(step.repeat_hi);
    }
  }
}

void ForEachSelectExpr(const SelectExpression* select,
                       const CovergroupExprVisitor& fn) {
  if (select == nullptr) return;
  ForEachRangeExpr(select->intersect, fn);
  fn(select->expr);
  fn(select->matches);
  ForEachSelectExpr(select->lhs, fn);
  ForEachSelectExpr(select->rhs, fn);
}

void ForEachCrossExpr(const CoverCrossDecl& cross,
                      const CovergroupExprVisitor& fn) {
  fn(cross.iff);
  for (const CrossBodyItem& item : cross.body) {
    fn(item.option.value);
    fn(item.bins.iff);
    ForEachSelectExpr(item.bins.select, fn);
  }
}

}  // namespace

void ForEachCovergroupExpr(const CovergroupDecl& group,
                           const CovergroupExprVisitor& fn) {
  for (const EventExpr& event : group.event.clocking) {
    fn(event.signal);
    fn(event.iff_condition);
  }
  for (const CoverageSpecOrOption& item : group.items) {
    fn(item.option.value);
    if (item.cover_point != nullptr) {
      fn(item.cover_point->expr);
      fn(item.cover_point->iff);
      for (const BinsOrOptions& bins : item.cover_point->bins)
        ForEachBinsExpr(bins, fn);
    }
    if (item.cover_cross != nullptr) ForEachCrossExpr(*item.cover_cross, fn);
  }
}

}  // namespace delta
