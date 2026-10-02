#include "parser/covergroup_sample_formal_uses.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

const Expr* FindNamedIdentifier(const Expr* e,
                                const std::vector<std::string_view>& names) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier &&
      std::find(names.begin(), names.end(), e->text) != names.end()) {
    return e;
  }
  for (const Expr* child : {e->lhs, e->rhs, e->condition, e->true_expr,
                            e->false_expr, e->base, e->index, e->index_end}) {
    if (const Expr* found = FindNamedIdentifier(child, names)) return found;
  }
  for (const std::vector<Expr*>* list : {&e->args, &e->elements}) {
    for (const Expr* child : *list) {
      if (const Expr* found = FindNamedIdentifier(child, names)) return found;
    }
  }
  return nullptr;
}

namespace {

// The sample formals of one covergroup and where their misuses are reported.
struct SampleFormalUses {
  std::vector<std::string_view> formals;
  DiagEngine& diag;

  // Reports each distinct formal `e` names, `context` saying what `e` is.
  void Report(const Expr* e, std::string_view context) const {
    std::vector<std::string_view> rest = formals;
    while (const Expr* formal = FindNamedIdentifier(e, rest)) {
      diag.Error(formal->range.start,
                 "sample method formal argument '" + std::string(formal->text) +
                     "' may only designate a coverpoint or conditional guard "
                     "expression, not " +
                     std::string(context),
                 Subclause("19.8.1"));
      std::erase(rest, formal->text);
    }
  }

  void ReportRanges(const std::vector<CovergroupValueRange>& ranges,
                    std::string_view context) const {
    for (const CovergroupValueRange& range : ranges) {
      Report(range.lo, context);
      Report(range.hi, context);
    }
  }
};

constexpr std::string_view kOptionValue = "a coverage-option value";
constexpr std::string_view kBinSpecification = "a bin specification";
constexpr std::string_view kSelectExpression = "a cross bin select expression";

void ReportInBins(const SampleFormalUses& uses, const BinsOrOptions& bins) {
  if (bins.kind == BinsOrOptionsKind::kOption) {
    uses.Report(bins.option.value, kOptionValue);
    return;
  }
  uses.Report(bins.array_size, kBinSpecification);
  uses.ReportRanges(bins.ranges, kBinSpecification);
  uses.Report(bins.with_expr, kBinSpecification);
  uses.Report(bins.set_expr, kBinSpecification);
  for (const TransSet& set : bins.transitions) {
    for (const TransRangeList& step : set.steps) {
      uses.ReportRanges(step.items, kBinSpecification);
      uses.Report(step.repeat_lo, kBinSpecification);
      uses.Report(step.repeat_hi, kBinSpecification);
    }
  }
}

void ReportInSelect(const SampleFormalUses& uses,
                    const SelectExpression* select) {
  if (select == nullptr) return;
  uses.ReportRanges(select->intersect, kSelectExpression);
  uses.Report(select->expr, kSelectExpression);
  uses.Report(select->matches, kSelectExpression);
  ReportInSelect(uses, select->lhs);
  ReportInSelect(uses, select->rhs);
}

void ReportInCross(const SampleFormalUses& uses, const CoverCrossDecl& cross) {
  for (const CrossBodyItem& item : cross.body) {
    if (item.kind == CrossBodyItemKind::kOption) {
      uses.Report(item.option.value, kOptionValue);
    } else if (item.kind == CrossBodyItemKind::kBinsSelection) {
      ReportInSelect(uses, item.bins.select);
    }
  }
}

}  // namespace

void ReportSampleFormalsOutsideCoverpoints(const CovergroupDecl& cg,
                                           DiagEngine& diag) {
  SampleFormalUses uses{{}, diag};
  for (const FunctionArg& formal : cg.event.sample_formals) {
    uses.formals.push_back(formal.name);
  }
  if (uses.formals.empty()) return;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kOption) {
      uses.Report(item.option.value, kOptionValue);
    } else if (item.kind == CoverageSpecKind::kCoverPoint) {
      for (const BinsOrOptions& bins : item.cover_point->bins) {
        ReportInBins(uses, bins);
      }
    } else {
      ReportInCross(uses, *item.cover_cross);
    }
  }
}

}  // namespace delta
