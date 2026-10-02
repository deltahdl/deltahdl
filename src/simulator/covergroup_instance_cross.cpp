#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <set>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// A cross product, as a tuple of indices into the bins of the crossed
// coverpoints, in the order the cross lists them (§19.6).
using Tuple = std::vector<size_t>;

// What a select_expression of a cross reads (§19.6.1): the instance, the
// index into its points of each coverpoint the cross crosses, the cross
// items as written, the cross's products, the values of each `intersect` the
// expression holds, and the products each `with` (§19.6.1.2) and
// cross_set_expression (§19.6.1.4) selects, each read once.
struct CrossSelector {
  const CovergroupInstance& inst;
  std::vector<size_t> points;
  std::vector<std::string_view> items;
  std::vector<Tuple> products;
  std::unordered_map<const SelectExpression*, std::vector<CoverValueRange>>
      intersects;
  std::unordered_map<const SelectExpression*, std::set<Tuple>> computed;
};

// §19.6: the coverpoint `name` of the instance, by index into its points; a
// variable the cross names that no coverpoint does is given an implicit
// coverpoint, as though `coverpoint name;` had been written.
size_t CrossedPoint(CovergroupInstance& inst, std::string_view name,
                    size_t index, SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < inst.points.size(); ++i) {
    if (inst.points[i].point->name == name) return i;
  }
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name;
  auto* decl = arena.Create<CoverPointDecl>();
  decl->expr = id;
  BuildCoverpoint(inst, *decl, index, ctx, arena);
  return inst.points.size() - 1;
}

// Reads the values of every `intersect` in a select_expression, a `$` bound
// standing for the end of the values of the coverpoint it names.
void ReadIntersects(const SelectExpression* select, CrossSelector& selector,
                    SimContext& ctx, Arena& arena) {
  if (select == nullptr) return;
  if (select->kind == SelectExpressionKind::kBinsOf &&
      !select->intersect.empty()) {
    for (size_t point : selector.points) {
      const SampledCoverpoint& sampled = selector.inst.points[point];
      if (sampled.point->name == select->bins_of) {
        selector.intersects[select] =
            CovergroupRangeValues(select->intersect, sampled, ctx, arena);
      }
    }
  }
  ReadIntersects(select->lhs, selector, ctx, arena);
  ReadIntersects(select->rhs, selector, ctx, arena);
}

bool InValues(int64_t v, const std::vector<CoverValueRange>& values) {
  return std::ranges::any_of(
      values, [&](const CoverValueRange& r) { return r.lo <= v && v <= r.hi; });
}

// §19.6.1: whether a coverpoint bin's values intersect `values`; a transition
// bin's values are the last of each of its transitions.
bool BinIntersects(const CoverBin& bin,
                   const std::vector<CoverValueRange>& values) {
  for (int64_t v : CoverageDB::BinsofBinValues(bin)) {
    if (InValues(v, values)) return true;
  }
  return std::ranges::any_of(bin.ranges, [&](const CoverValueRange& r) {
    return std::ranges::any_of(values, [&](const CoverValueRange& v) {
      return v.lo <= r.hi && r.lo <= v.hi;
    });
  });
}

// §19.6.1: whether the bin `bin` of a coverpoint is the one, or one of the
// array of bins, that `binsof ( cover_point . bin )` names.
bool BinNamed(const CoverBin& bin, std::string_view name) {
  return bin.name == name ||
         (bin.name.starts_with(name) && bin.name.size() > name.size() &&
          bin.name[name.size()] == '[');
}

bool SelectsBinsOf(const SelectExpression& select, const Tuple& tuple,
                   const CrossSelector& selector) {
  for (size_t i = 0; i < selector.points.size(); ++i) {
    const CoverPoint& cp = *selector.inst.points[selector.points[i]].point;
    if (cp.name != select.bins_of) continue;
    const CoverBin& bin = cp.bins[tuple[i]];
    if (!select.bins_of_bin.empty() && !BinNamed(bin, select.bins_of_bin)) {
      return false;
    }
    auto it = selector.intersects.find(&select);
    return it == selector.intersects.end() || BinIntersects(bin, it->second);
  }
  return false;
}

// §19.6.1: whether a select_expression selects the cross product `tuple`.
bool Selects(const SelectExpression& select, const Tuple& tuple,
             const CrossSelector& selector) {
  switch (select.kind) {
    case SelectExpressionKind::kBinsOf:
      return SelectsBinsOf(select, tuple, selector);
    case SelectExpressionKind::kNot:
      return !Selects(*select.lhs, tuple, selector);
    case SelectExpressionKind::kAnd:
      return Selects(*select.lhs, tuple, selector) &&
             Selects(*select.rhs, tuple, selector);
    case SelectExpressionKind::kOr:
      return Selects(*select.lhs, tuple, selector) ||
             Selects(*select.rhs, tuple, selector);
    case SelectExpressionKind::kParenthesized:
      return Selects(*select.lhs, tuple, selector);
    case SelectExpressionKind::kCrossIdentifier:
      return true;
    case SelectExpressionKind::kWith:
    case SelectExpressionKind::kCrossSet: {
      auto it = selector.computed.find(&select);
      return it != selector.computed.end() && it->second.contains(tuple);
    }
  }
  return false;
}

// §19.6.1.2 and §19.6.1.4: how many value tuples of a bin tuple a selection
// requires, the `matches` count, every one of them for `matches $`, or one
// where no `matches` is written.
struct MatchPolicy {
  bool all = false;
  uint64_t count = 1;

  bool Met(uint64_t satisfied, uint64_t total) const {
    return all ? total > 0 && satisfied == total : satisfied >= count;
  }
};

MatchPolicy ReadPolicy(const SelectExpression& select, SimContext& ctx,
                       Arena& arena) {
  if (select.matches_dollar) return {true, 0};
  if (select.matches == nullptr) return {};
  return {false, static_cast<uint64_t>(std::max<int64_t>(
                     1, CovergroupInt(select.matches, ctx, arena)))};
}

// The values of each coverpoint bin of the bin tuple `tuple`, as sorted
// disjoint spans; a transition bin's values are the last of each of its
// transitions.
std::vector<std::vector<CoverValueRange>> TupleSpans(
    const Tuple& tuple, const CrossSelector& selector) {
  std::vector<std::vector<CoverValueRange>> spans;
  for (size_t i = 0; i < selector.points.size(); ++i) {
    const CoverBin& bin =
        selector.inst.points[selector.points[i]].point->bins[tuple[i]];
    std::vector<CoverValueRange> values = bin.ranges;
    for (int64_t v : CoverageDB::BinsofBinValues(bin)) values.push_back({v, v});
    spans.push_back(NormalizeSpans(std::move(values)));
  }
  return spans;
}

// How many value tuples a bin tuple of these spans holds, saturating.
uint64_t ValueTupleCount(
    const std::vector<std::vector<CoverValueRange>>& spans) {
  uint64_t total = 1;
  for (const auto& point_spans : spans) {
    uint64_t values = 0;
    for (const CoverValueRange& r : point_spans) {
      // A span over every int64_t holds 2^64 values, which reads as 0 here.
      uint64_t size =
          static_cast<uint64_t>(r.hi) - static_cast<uint64_t>(r.lo) + 1;
      values =
          size == 0 || values > UINT64_MAX - size ? UINT64_MAX : values + size;
    }
    total = values != 0 && total > UINT64_MAX / values ? UINT64_MAX
                                                       : total * values;
  }
  return total;
}

// §19.6.1.2: evaluates a with_covergroup_expression for the value tuples of
// a bin tuple, each cross item bound to its value as its coverpoint's type
// holds it, until the policy is settled either way.
class WithEvaluation {
 public:
  WithEvaluation(const Expr* expr, MatchPolicy policy,
                 const CrossSelector& selector, SimContext& ctx, Arena& arena)
      : expr_(expr), policy_(policy), ctx_(ctx), arena_(arena) {
    for (size_t i = 0; i < selector.points.size(); ++i) {
      const SampledCoverpoint& point = selector.inst.points[selector.points[i]];
      Variable* var = ctx.CreateLocalVariable(selector.items[i], point.width,
                                              point.is_signed);
      var->value = MakeLogic4VecVal(arena, point.width, 0);
      var->value.is_signed = point.is_signed;
      vars_.push_back(var);
      masks_.push_back(point.width >= 64 ? UINT64_MAX
                                         : (uint64_t{1} << point.width) - 1);
    }
  }

  bool Selects(const std::vector<std::vector<CoverValueRange>>& spans) {
    satisfied_ = 0;
    evaluated_ = 0;
    Visit(spans, 0);
    return policy_.Met(satisfied_, evaluated_);
  }

 private:
  // Binds the values of the spans from the point `i` on, evaluating the
  // expression for each value tuple; false once the outcome is settled.
  bool Visit(const std::vector<std::vector<CoverValueRange>>& spans, size_t i) {
    if (i == spans.size()) return Evaluate();
    for (const CoverValueRange& r : spans[i]) {
      for (int64_t v = r.lo;; ++v) {
        vars_[i]->value.words[0].aval = static_cast<uint64_t>(v) & masks_[i];
        if (!Visit(spans, i + 1)) return false;
        if (v == r.hi) break;
      }
    }
    return true;
  }

  bool Evaluate() {
    ++evaluated_;
    if (EvalExpr(expr_, ctx_, arena_).IsTruthy()) ++satisfied_;
    if (policy_.all) return satisfied_ == evaluated_;
    return satisfied_ < policy_.count;
  }

  const Expr* expr_;
  MatchPolicy policy_;
  SimContext& ctx_;
  Arena& arena_;
  std::vector<Variable*> vars_;
  std::vector<uint64_t> masks_;
  uint64_t satisfied_ = 0;
  uint64_t evaluated_ = 0;
};

// §19.6.1.2: the bin tuples the subordinate select_expression selects for
// which enough value tuples make the with_covergroup_expression true.
std::set<Tuple> WithSelections(const SelectExpression& select,
                               const CrossSelector& selector, SimContext& ctx,
                               Arena& arena) {
  MatchPolicy policy = ReadPolicy(select, ctx, arena);
  std::set<Tuple> chosen;
  ctx.PushScope();
  WithEvaluation evaluation(select.expr, policy, selector, ctx, arena);
  for (const Tuple& tuple : selector.products) {
    if (Selects(*select.lhs, tuple, selector) &&
        evaluation.Selects(TupleSpans(tuple, selector))) {
      chosen.insert(tuple);
    }
  }
  ctx.PopScope();
  return chosen;
}

// §19.6.1.4: the value tuples a cross_set_expression lists, written as an
// array literal of one array literal per tuple, each value as its
// coverpoint's type holds it.
std::set<std::vector<int64_t>> CrossSetValueTuples(
    const Expr* e, const CrossSelector& selector, SimContext& ctx,
    Arena& arena) {
  std::set<std::vector<int64_t>> tuples;
  e = UnwrapTypedPattern(e);
  if (e->kind != ExprKind::kAssignmentPattern) return tuples;
  for (const Expr* element : e->elements) {
    element = UnwrapTypedPattern(element);
    if (element->kind != ExprKind::kAssignmentPattern ||
        element->elements.size() != selector.points.size()) {
      continue;
    }
    std::vector<int64_t> values;
    values.reserve(selector.points.size());
    for (size_t i = 0; i < selector.points.size(); ++i) {
      values.push_back(
          ConvertToPointType(EvalExpr(element->elements[i], ctx, arena),
                             selector.inst.points[selector.points[i]]));
    }
    tuples.insert(std::move(values));
  }
  return tuples;
}

// §19.6.1.4: the bin tuples holding enough of the value tuples a
// cross_set_expression lists.
std::set<Tuple> CrossSetSelections(const SelectExpression& select,
                                   const CrossSelector& selector,
                                   SimContext& ctx, Arena& arena) {
  MatchPolicy policy = ReadPolicy(select, ctx, arena);
  std::set<std::vector<int64_t>> listed =
      CrossSetValueTuples(select.expr, selector, ctx, arena);
  std::set<Tuple> chosen;
  for (const Tuple& tuple : selector.products) {
    std::vector<std::vector<CoverValueRange>> spans =
        TupleSpans(tuple, selector);
    auto held = static_cast<uint64_t>(
        std::ranges::count_if(listed, [&](const auto& values) {
          for (size_t i = 0; i < values.size(); ++i) {
            if (!InValues(values[i], spans[i])) return false;
          }
          return true;
        }));
    if (policy.Met(held, ValueTupleCount(spans))) chosen.insert(tuple);
  }
  return chosen;
}

// Reads the products each `with` and cross_set_expression of a
// select_expression selects, those it is built on first.
void ReadComputedSelections(const SelectExpression* select,
                            CrossSelector& selector, SimContext& ctx,
                            Arena& arena) {
  if (select == nullptr) return;
  ReadComputedSelections(select->lhs, selector, ctx, arena);
  ReadComputedSelections(select->rhs, selector, ctx, arena);
  if (select->kind == SelectExpressionKind::kWith) {
    selector.computed[select] = WithSelections(*select, selector, ctx, arena);
  } else if (select->kind == SelectExpressionKind::kCrossSet) {
    selector.computed[select] =
        CrossSetSelections(*select, selector, ctx, arena);
  }
}

// A cross's bins_selection items read as the products each selects: the
// `bins` (§19.6.1), and the products ignore_bins (§19.6.2) and illegal_bins
// (§19.6.3) take out of every bin of the cross.
struct CrossSelections {
  std::vector<CrossBin> user_bins;
  std::vector<const Expr*> user_guards;
  std::set<Tuple> in_user_bins;
  std::set<Tuple> excluded;
};

CrossSelections ReadSelections(const CoverCrossDecl& decl,
                               const std::vector<Tuple>& products,
                               const CrossSelector& selector,
                               SampledCross& sampled) {
  CrossSelections selections;
  for (const CrossBodyItem& item : decl.body) {
    if (item.kind != CrossBodyItemKind::kBinsSelection) continue;
    std::vector<Tuple> selected;
    for (const Tuple& tuple : products) {
      if (Selects(*item.bins.select, tuple, selector))
        selected.push_back(tuple);
    }
    if (item.bins.keyword == BinsKeyword::kBins) {
      selections.in_user_bins.insert(selected.begin(), selected.end());
      CrossBin bin;
      bin.name = std::string(item.bins.name);
      bin.bin_tuples = std::move(selected);
      selections.user_bins.push_back(std::move(bin));
      selections.user_guards.push_back(item.bins.iff);
      continue;
    }
    selections.excluded.insert(selected.begin(), selected.end());
    if (item.bins.keyword == BinsKeyword::kIllegalBins) {
      sampled.illegal.push_back({std::string(item.bins.name), selected});
    }
  }
  return selections;
}

// The cross's bins: each user-defined bin with the products ignore_bins and
// illegal_bins take out removed, a bin left with none taking no part
// (§19.11.2); then an automatic bin for every other product that no
// user-defined bin selects, or none at all where cross_retain_auto_bins is
// false and the cross defines a bin of its own (§19.6.1, Table 19-1).
void AddCrossBins(const CovergroupInstance& inst, CrossCover& cross,
                  const std::vector<Tuple>& products,
                  CrossSelections& selections, SampledCross& sampled) {
  for (size_t i = 0; i < selections.user_bins.size(); ++i) {
    CrossBin& bin = selections.user_bins[i];
    std::erase_if(bin.bin_tuples, [&](const Tuple& t) {
      return selections.excluded.contains(t);
    });
    if (bin.bin_tuples.empty()) continue;
    if (selections.user_guards[i] != nullptr) {
      sampled.bin_guards.emplace_back(cross.bins.size(),
                                      selections.user_guards[i]);
    }
    cross.bins.push_back(std::move(bin));
  }
  bool retain =
      cross.option.cross_retain_auto_bins || selections.user_bins.empty();
  for (const Tuple& tuple : products) {
    if (!retain || selections.in_user_bins.contains(tuple) ||
        selections.excluded.contains(tuple)) {
      continue;
    }
    CrossBin bin;
    bin.name = CoverageDB::CrossProductName(inst.group, &cross, tuple);
    bin.bin_tuples.push_back(tuple);
    cross.bins.push_back(std::move(bin));
  }
  for (CrossBin& bin : cross.bins) {
    bin.at_least = static_cast<uint32_t>(std::max(0, cross.option.at_least));
  }
}

}  // namespace

void BuildCross(CovergroupInstance& inst, const CoverCrossDecl& decl,
                size_t index, SimContext& ctx, Arena& arena) {
  CrossCover cross;
  cross.name = decl.label.empty() ? std::format("__cross_{}", index)
                                  : std::string(decl.label);
  cross.option.at_least = inst.group->options.at_least;
  cross.option.cross_num_print_missing =
      inst.group->options.cross_num_print_missing;
  cross.option.cross_retain_auto_bins =
      inst.group->options.cross_retain_auto_bins;
  for (const CrossBodyItem& item : decl.body) {
    if (item.kind == CrossBodyItemKind::kOption) {
      ApplyCrossOption(cross, item.option, ctx, arena);
    }
  }
  std::vector<size_t> points;
  std::vector<std::string_view> items;
  for (const CrossItem& item : decl.items) {
    points.push_back(CrossedPoint(inst, item.name, index, ctx, arena));
    items.push_back(item.name);
    cross.coverpoint_names.push_back(inst.points[points.back()].point->name);
  }
  SampledCross sampled;
  sampled.index = inst.group->crosses.size();
  sampled.iff = decl.iff;
  CrossCover* added = CoverageDB::AddCross(inst.group, std::move(cross));
  CrossSelector selector{inst,
                         std::move(points),
                         std::move(items),
                         CoverageDB::CrossProductTuples(inst.group, added),
                         {},
                         {}};
  for (const CrossBodyItem& item : decl.body) {
    if (item.kind == CrossBodyItemKind::kBinsSelection) {
      ReadIntersects(item.bins.select, selector, ctx, arena);
      ReadComputedSelections(item.bins.select, selector, ctx, arena);
    }
  }
  CrossSelections selections =
      ReadSelections(decl, selector.products, selector, sampled);
  AddCrossBins(inst, *added, selector.products, selections, sampled);
  inst.crosses.push_back(std::move(sampled));
}

}  // namespace delta
