#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// The values of a covergroup_range_list in the order written, duplicates
// retained (§19.5.1), a single value held as a span of one.
using ValueList = std::vector<CoverValueRange>;

constexpr uint64_t kAllValues = std::numeric_limits<uint64_t>::max();

// How many values a span holds; the 2^64 of a span over every int64_t, which
// do not fit, read as the most a count can hold.
uint64_t SpanSize(const CoverValueRange& r) {
  uint64_t size = static_cast<uint64_t>(r.hi) - static_cast<uint64_t>(r.lo);
  return size == kAllValues ? kAllValues : size + 1;
}

uint64_t SaturatingAdd(uint64_t a, uint64_t b) {
  return a > kAllValues - b ? kAllValues : a + b;
}

uint64_t CountValues(const ValueList& list) {
  uint64_t count = 0;
  for (const CoverValueRange& r : list)
    count = SaturatingAdd(count, SpanSize(r));
  return count;
}

// Appends `v` to `list`, extending the last span where `v` follows it.
void AppendValue(ValueList& list, int64_t v) {
  if (!list.empty() && list.back().hi != std::numeric_limits<int64_t>::max() &&
      list.back().hi + 1 == v) {
    list.back().hi = v;
    return;
  }
  list.push_back({v, v});
}

// §19.5.4: each x, z or ? bit of a wildcard bin's value matches 0 and 1, so
// the value stands for every value filling those bits both ways. The bits the
// coverpoint has above the literal's width are 0.
void AppendWildcardValue(const Logic4Vec& v, const SampledCoverpoint& point,
                         ValueList& out) {
  uint64_t unknown = v.words[0].bval;
  if (v.width < 64) unknown &= (uint64_t{1} << v.width) - 1;
  uint32_t width = std::min<uint32_t>(point.width, 63);
  for (int64_t value : CoverageDB::ExpandWildcardValue(
           static_cast<int64_t>(v.words[0].aval & ~unknown), ~unknown, width)) {
    AppendValue(out, value);
  }
}

// §19.5.1: the values one covergroup_value_range adds, a `$` bound standing
// for the end of the coverpoint's values; §11.4.13: a tolerance range is the
// span around its center.
void AppendValueRange(const CovergroupValueRange& range,
                      const SampledCoverpoint& point, SimContext& ctx,
                      Arena& arena, ValueList& out) {
  CoverValueRange bounds = PointTypeBounds(point);
  if (range.kind == CovergroupValueRangeKind::kValue) {
    int64_t v = CovergroupInt(range.lo, ctx, arena);
    out.push_back({v, v});
    return;
  }
  if (range.kind == CovergroupValueRangeKind::kRange) {
    int64_t lo =
        range.lo != nullptr ? CovergroupInt(range.lo, ctx, arena) : bounds.lo;
    int64_t hi =
        range.hi != nullptr ? CovergroupInt(range.hi, ctx, arena) : bounds.hi;
    if (lo <= hi) out.push_back({lo, hi});
    return;
  }
  auto [lo, hi] = CoverageDB::ToleranceRange(
      CovergroupReal(range.lo, ctx, arena),
      CovergroupReal(range.hi, ctx, arena),
      range.kind == CovergroupValueRangeKind::kRelativeTolerance);
  if (std::ceil(lo) <= std::floor(hi)) {
    out.push_back({static_cast<int64_t>(std::ceil(lo)),
                   static_cast<int64_t>(std::floor(hi))});
  }
}

ValueList ReadRangeList(const std::vector<CovergroupValueRange>& ranges,
                        bool wildcard, const SampledCoverpoint& point,
                        SimContext& ctx, Arena& arena) {
  ValueList values;
  for (const CovergroupValueRange& range : ranges) {
    if (wildcard && range.kind == CovergroupValueRangeKind::kValue) {
      Logic4Vec v = EvalExpr(range.lo, ctx, arena);
      if (!v.IsKnown()) {
        AppendWildcardValue(v, point, values);
        continue;
      }
    }
    AppendValueRange(range, point, ctx, arena, values);
  }
  return values;
}

// §19.5.1.1: the values of `list` for which `with_expr` is true, in order,
// the name `item` standing for the candidate value as the coverpoint's type.
ValueList FilterWith(const ValueList& list, const Expr* with_expr,
                     const SampledCoverpoint& point, SimContext& ctx,
                     Arena& arena) {
  ctx.PushScope();
  Variable* item =
      ctx.CreateLocalVariable("item", point.width, point.is_signed);
  item->value = MakeLogic4VecVal(arena, point.width, 0);
  item->value.is_signed = point.is_signed;
  uint64_t mask =
      point.width >= 64 ? kAllValues : (uint64_t{1} << point.width) - 1;
  ValueList kept;
  for (const CoverValueRange& r : list) {
    for (int64_t v = r.lo;; ++v) {
      item->value.words[0].aval = static_cast<uint64_t>(v) & mask;
      if (EvalExpr(with_expr, ctx, arena).IsTruthy()) AppendValue(kept, v);
      if (v == r.hi) break;
    }
  }
  ctx.PopScope();
  return kept;
}

// §19.5.1.2: the elements of the array a set_covergroup_expression names, in
// order.
ValueList SetExpressionValues(const Expr* e, SimContext& ctx, Arena& arena) {
  ValueList values;
  const ArrayInfo* info =
      e->kind == ExprKind::kIdentifier ? ctx.FindArrayInfo(e->text) : nullptr;
  if (info == nullptr) return values;
  for (const Logic4Vec& element :
       CollectVecElements(e->text, *info, ctx, arena)) {
    AppendValue(values, SelectBoundValue(element));
  }
  return values;
}

// The values of `list` at the positions [begin, end) of its order.
ValueList SliceValues(const ValueList& list, uint64_t begin, uint64_t end) {
  ValueList slice;
  uint64_t pos = 0;
  for (const CoverValueRange& r : list) {
    uint64_t next = SaturatingAdd(pos, SpanSize(r));
    uint64_t lo = std::max(pos, begin);
    uint64_t hi = std::min(next, end);
    if (lo < hi) {
      auto first = static_cast<uint64_t>(r.lo);
      slice.push_back({static_cast<int64_t>(first + (lo - pos)),
                       static_cast<int64_t>(first + (hi - pos - 1))});
    }
    pos = next;
    if (pos >= end) break;
  }
  return slice;
}

std::vector<int64_t> ExpandValues(const ValueList& list) {
  std::vector<int64_t> values;
  for (const CoverValueRange& r : list) {
    for (int64_t v = r.lo;; ++v) {
      values.push_back(v);
      if (v == r.hi) break;
    }
  }
  return values;
}

CoverBinKind BinKindOf(BinsKeyword keyword) {
  if (keyword == BinsKeyword::kIllegalBins) return CoverBinKind::kIllegal;
  if (keyword == BinsKeyword::kIgnoreBins) return CoverBinKind::kIgnore;
  return CoverBinKind::kExplicit;
}

// Adds `bin` to the coverpoint, keeping the guard of a definition that ends
// in `iff` (§19.5.1).
void AddGuardedBin(SampledCoverpoint& point, const BinsOrOptions& bins,
                   CoverBin bin) {
  size_t index = point.point->bins.size();
  CoverageDB::AddBin(point.point, std::move(bin));
  if (bins.iff != nullptr) point.bin_guards.emplace_back(index, bins.iff);
}

// The values a bins definition holds, and the `with` that the
// distribute_first type option holds back until they are distributed, null
// where none is (§19.5.1.1).
struct BinValues {
  ValueList values;
  const Expr* with_each = nullptr;
};

// §19.5.1: one bin for all the values, one per distinct value for `[]`, or
// the values spread over the N bins of `[N]`, B = values / N to each and the
// rest to the last, with a bin past the values left empty. A `with` held back
// is applied to each bin's values (§19.5.1.1).
void AddValueBins(SampledCoverpoint& point, const BinsOrOptions& bins,
                  const BinValues& held, SimContext& ctx, Arena& arena) {
  auto filtered = [&](const ValueList& list) {
    return held.with_each != nullptr
               ? FilterWith(list, held.with_each, point, ctx, arena)
               : list;
  };
  CoverBin bin;
  bin.kind = BinKindOf(bins.keyword);
  if (!bins.is_array) {
    bin.name = std::string(bins.name);
    bin.ranges = filtered(held.values);
    AddGuardedBin(point, bins, std::move(bin));
    return;
  }
  if (bins.array_size == nullptr) {
    for (CoverBin& each : CoverageDB::OpenArrayValueBins(
             bins.name, ExpandValues(filtered(held.values)))) {
      each.kind = bin.kind;
      AddGuardedBin(point, bins, std::move(each));
    }
    return;
  }
  auto count = static_cast<uint64_t>(
      std::max<int64_t>(1, CovergroupInt(bins.array_size, ctx, arena)));
  uint64_t total = CountValues(held.values);
  uint64_t per_bin = std::max<uint64_t>(1, total / count);
  for (uint64_t i = 0; i < count; ++i) {
    uint64_t begin = i > total / per_bin ? total : std::min(total, i * per_bin);
    uint64_t end = i + 1 == count ? total : std::min(total, begin + per_bin);
    bin.name = CoverageDB::StateBinName(bins.name, static_cast<int64_t>(i));
    bin.ranges = filtered(SliceValues(held.values, begin, end));
    AddGuardedBin(point, bins, bin);
  }
}

// §19.5.1 and §19.5.1.1: the bins of a covergroup_range_list, or for
// `cover_point_identifier with` of every value of the coverpoint, filtered by
// the definition's `with` before they are distributed unless the
// distribute_first type option is set.
void AddRangeListBins(const CovergroupInstance& inst, SampledCoverpoint& point,
                      const BinsOrOptions& bins, SimContext& ctx,
                      Arena& arena) {
  ValueList values =
      bins.kind == BinsOrOptionsKind::kCoverPointWith
          ? ValueList{PointTypeBounds(point)}
          : ReadRangeList(bins.ranges, bins.wildcard, point, ctx, arena);
  if (bins.with_expr == nullptr || inst.group->type_option.distribute_first) {
    AddValueBins(point, bins, {std::move(values), bins.with_expr}, ctx, arena);
    return;
  }
  AddValueBins(point, bins,
               {FilterWith(values, bins.with_expr, point, ctx, arena), nullptr},
               ctx, arena);
}

// One trans_range_list of a transition (§19.5.2): the values its trans_item
// lists, and the repetition that follows it with its bounds.
struct TransStep {
  std::vector<int64_t> values;
  TransRepetition repetition = TransRepetition::kNone;
  uint32_t lo = 1;
  uint32_t hi = 1;
};

TransStep ReadTransStep(const TransRangeList& list, bool wildcard,
                        const SampledCoverpoint& point, SimContext& ctx,
                        Arena& arena) {
  TransStep step;
  step.values =
      ExpandValues(ReadRangeList(list.items, wildcard, point, ctx, arena));
  step.repetition = list.repetition;
  if (list.repeat_lo != nullptr) {
    step.lo = static_cast<uint32_t>(CovergroupInt(list.repeat_lo, ctx, arena));
    step.hi =
        list.repeat_hi != nullptr
            ? static_cast<uint32_t>(CovergroupInt(list.repeat_hi, ctx, arena))
            : step.lo;
  }
  return step;
}

bool RepeatsUnbounded(const TransStep& step) {
  return step.repetition == TransRepetition::kGoto ||
         step.repetition == TransRepetition::kNonconsecutive;
}

// Each of `heads` followed by each of `tails`.
void AppendProducts(const std::vector<std::vector<int64_t>>& heads,
                    const std::vector<std::vector<int64_t>>& tails,
                    std::vector<std::vector<int64_t>>& out) {
  for (const auto& tail : tails) {
    for (const auto& head : heads) {
      out.push_back(head);
      out.back().insert(out.back().end(), tail.begin(), tail.end());
    }
  }
}

// §19.5.2: the sequences a trans_set of bounded steps expands to, each value
// list crossed with the next and `[* lo:hi]` repeating its item lo to hi
// times.
std::vector<std::vector<int64_t>> ExpandTransSet(
    const std::vector<TransStep>& steps) {
  std::vector<std::vector<int64_t>> sequences = {{}};
  for (const TransStep& step : steps) {
    bool repeats = step.repetition == TransRepetition::kConsecutive;
    std::vector<std::vector<int64_t>> next;
    for (uint32_t n = repeats ? step.lo : 1; n <= (repeats ? step.hi : 1);
         ++n) {
      std::vector<std::vector<int64_t>> repeated(n, step.values);
      AppendProducts(sequences, CoverageDB::ExpandSetTransition(repeated),
                     next);
    }
    sequences = std::move(next);
  }
  return sequences;
}

// §19.5.2: the patterns a trans_set holding a goto `[-> ]` or nonconsecutive
// `[= ]` repetition matches, a consecutive repetition written out as that
// many plain elements.
std::vector<std::vector<TransitionPatternElement>> TransSetPatterns(
    const std::vector<TransStep>& steps) {
  std::vector<std::vector<TransitionPatternElement>> patterns = {{}};
  for (const TransStep& step : steps) {
    TransitionPatternElement element;
    element.values = step.values;
    if (RepeatsUnbounded(step)) {
      element.has_repeat = true;
      element.repeat_kind = step.repetition == TransRepetition::kGoto
                                ? TransitionRepeatKind::kGoto
                                : TransitionRepeatKind::kNonconsecutive;
      element.repeat_lo = step.lo;
      element.repeat_hi = step.hi;
    }
    bool repeats = step.repetition == TransRepetition::kConsecutive;
    std::vector<std::vector<TransitionPatternElement>> next;
    for (uint32_t n = repeats ? step.lo : 1; n <= (repeats ? step.hi : 1);
         ++n) {
      for (const auto& head : patterns) {
        next.push_back(head);
        next.back().insert(next.back().end(), n, element);
      }
    }
    patterns = std::move(next);
  }
  return patterns;
}

// §19.5.2: a transition bin holding every sequence its trans_list writes, or
// for `[]` one bin per sequence; §19.5.5 and §19.5.6: an ignore_bins or
// illegal_bins of transitions.
void AddTransitionBins(SampledCoverpoint& point, const BinsOrOptions& bins,
                       SimContext& ctx, Arena& arena) {
  CoverBin bin;
  bin.name = std::string(bins.name);
  bin.kind = bins.keyword == BinsKeyword::kBins ? CoverBinKind::kTransition
                                                : BinKindOf(bins.keyword);
  for (const TransSet& set : bins.transitions) {
    std::vector<TransStep> steps;
    steps.reserve(set.steps.size());
    for (const TransRangeList& list : set.steps) {
      steps.push_back(ReadTransStep(list, bins.wildcard, point, ctx, arena));
    }
    if (std::ranges::any_of(steps, RepeatsUnbounded)) {
      for (auto& pattern : TransSetPatterns(steps)) {
        bin.transition_patterns.push_back(std::move(pattern));
      }
      continue;
    }
    for (auto& sequence : ExpandTransSet(steps)) {
      bin.transitions.push_back(std::move(sequence));
    }
  }
  if (!bins.is_array || !bin.transition_patterns.empty()) {
    AddGuardedBin(point, bins, std::move(bin));
    return;
  }
  for (const auto& sequence : bin.transitions) {
    CoverBin each;
    each.name = CoverageDB::TransitionArrayBinName(bins.name, sequence);
    each.kind = bin.kind;
    each.transitions = {sequence};
    AddGuardedBin(point, bins, std::move(each));
  }
}

// Sorts and joins overlapping and adjacent spans.
ValueList Normalize(ValueList list) {
  std::ranges::sort(list, {}, &CoverValueRange::lo);
  ValueList joined;
  for (const CoverValueRange& r : list) {
    if (!joined.empty() &&
        (joined.back().hi == std::numeric_limits<int64_t>::max() ||
         r.lo <= joined.back().hi + 1)) {
      joined.back().hi = std::max(joined.back().hi, r.hi);
      continue;
    }
    joined.push_back(r);
  }
  return joined;
}

// The spans of `r` left once the sorted, disjoint `excluded` are taken out.
void SubtractSpans(const CoverValueRange& r, const ValueList& excluded,
                   ValueList& out) {
  int64_t cursor = r.lo;
  for (const CoverValueRange& e : excluded) {
    if (e.hi < cursor) continue;
    if (e.lo > r.hi) break;
    if (e.lo > cursor) out.push_back({cursor, e.lo - 1});
    if (e.hi >= r.hi) return;
    cursor = e.hi + 1;
  }
  out.push_back({cursor, r.hi});
}

// §19.5.5 and §19.5.6: a value an ignore_bins or illegal_bins holds is
// excluded from coverage, so it is taken out of the coverpoint's other value
// bins, automatic ones included, after their values are distributed; a bin it
// leaves holding nothing takes no part in coverage (§19.11.1).
void ExcludeIgnoredAndIllegalValues(CoverPoint* cp) {
  ValueList excluded;
  for (const CoverBin& bin : cp->bins) {
    if (bin.kind != CoverBinKind::kIgnore && bin.kind != CoverBinKind::kIllegal)
      continue;
    for (int64_t v : bin.values) excluded.push_back({v, v});
    excluded.insert(excluded.end(), bin.ranges.begin(), bin.ranges.end());
  }
  if (excluded.empty()) return;
  excluded = Normalize(std::move(excluded));
  for (CoverBin& bin : cp->bins) {
    if (bin.kind != CoverBinKind::kExplicit && bin.kind != CoverBinKind::kAuto)
      continue;
    std::erase_if(bin.values, [&](int64_t v) {
      return std::ranges::any_of(excluded, [&](const CoverValueRange& e) {
        return e.lo <= v && v <= e.hi;
      });
    });
    ValueList kept;
    for (const CoverValueRange& r : bin.ranges)
      SubtractSpans(r, excluded, kept);
    bin.ranges = std::move(kept);
  }
}

// One item of a real coverpoint's covergroup_range_list (§19.5.1): a value,
// as an interval holding it alone, or a range, a `$` bound reaching without
// end.
struct RealItem {
  RealInterval interval;
  bool is_value = false;
  bool uses_dollar = false;
};

std::vector<RealItem> ReadRealItems(const BinsOrOptions& bins, SimContext& ctx,
                                    Arena& arena) {
  constexpr double kInf = std::numeric_limits<double>::infinity();
  std::vector<RealItem> items;
  for (const CovergroupValueRange& range : bins.ranges) {
    RealItem item;
    if (range.kind == CovergroupValueRangeKind::kValue) {
      double v = CovergroupReal(range.lo, ctx, arena);
      item.interval = {v, v, true};
      item.is_value = true;
    } else if (range.kind == CovergroupValueRangeKind::kRange) {
      item.interval = {
          range.lo != nullptr ? CovergroupReal(range.lo, ctx, arena) : -kInf,
          range.hi != nullptr ? CovergroupReal(range.hi, ctx, arena) : kInf,
          true};
      item.uses_dollar = range.lo == nullptr || range.hi == nullptr;
    } else {
      auto [lo, hi] = CoverageDB::ToleranceRange(
          CovergroupReal(range.lo, ctx, arena),
          CovergroupReal(range.hi, ctx, arena),
          range.kind == CovergroupValueRangeKind::kRelativeTolerance);
      item.interval = {lo, hi, true};
    }
    items.push_back(item);
  }
  return items;
}

// §19.5.1: the items an array of real bins is made of, each range divided
// into intervals of type_option.real_interval unless a `$` bounds it.
std::vector<RealItem> PartitionRealItems(const std::vector<RealItem>& items,
                                         double real_interval) {
  std::vector<RealItem> parts;
  for (const RealItem& item : items) {
    if (item.is_value) {
      parts.push_back(item);
      continue;
    }
    for (const RealInterval& interval :
         CoverageDB::RealRangeIntervals(item.interval.low, item.interval.high,
                                        real_interval, item.uses_dollar)) {
      parts.push_back({interval, false, item.uses_dollar});
    }
  }
  return parts;
}

std::string RealItemName(std::string_view base, const RealItem& item) {
  return item.is_value ? CoverageDB::RealValueBinName(base, item.interval.low)
                       : CoverageDB::RealIntervalBinName(base, item.interval);
}

// §19.5.1: the bins of `[N]` over a real coverpoint's values and intervals,
// B = items / N to each and the rest to the last.
void AddRealBinArray(SampledCoverpoint& point, const BinsOrOptions& bins,
                     const std::vector<RealItem>& parts, SimContext& ctx,
                     Arena& arena) {
  auto count = static_cast<size_t>(
      std::max<int64_t>(1, CovergroupInt(bins.array_size, ctx, arena)));
  size_t per_bin = std::max<size_t>(1, parts.size() / count);
  CoverBin bin;
  bin.kind = BinKindOf(bins.keyword);
  for (size_t i = 0; i < count; ++i) {
    size_t begin = std::min(parts.size(), i * per_bin);
    size_t end =
        i + 1 == count ? parts.size() : std::min(parts.size(), begin + per_bin);
    bin.name = CoverageDB::StateBinName(bins.name, static_cast<int64_t>(i));
    bin.real_intervals.clear();
    for (size_t j = begin; j < end; ++j) {
      bin.real_intervals.push_back(parts[j].interval);
    }
    AddGuardedBin(point, bins, bin);
  }
}

// §19.5.1: the bins of a real coverpoint, one for all of a definition's values
// and ranges, one per value and interval for `[]`, the identical intervals of
// several ranges merged, or its values and intervals spread over the N bins of
// `[N]`.
void AddRealBins(SampledCoverpoint& point, const BinsOrOptions& bins,
                 SimContext& ctx, Arena& arena) {
  CoverBin bin;
  bin.kind = BinKindOf(bins.keyword);
  std::vector<RealItem> items = ReadRealItems(bins, ctx, arena);
  if (!bins.is_array) {
    bin.name = std::string(bins.name);
    for (const RealItem& item : items)
      bin.real_intervals.push_back(item.interval);
    AddGuardedBin(point, bins, std::move(bin));
    return;
  }
  std::vector<RealItem> parts =
      PartitionRealItems(items, point.type_option.real_interval);
  if (bins.array_size != nullptr) {
    AddRealBinArray(point, bins, parts, ctx, arena);
    return;
  }
  std::vector<RealInterval> intervals;
  intervals.reserve(parts.size());
  for (const RealItem& part : parts) intervals.push_back(part.interval);
  for (const RealInterval& interval :
       CoverageDB::MergeIdenticalIntervals(intervals)) {
    RealItem item{interval, interval.low == interval.high, false};
    bin.name = RealItemName(bins.name, item);
    bin.real_intervals = {interval};
    AddGuardedBin(point, bins, bin);
  }
}

void AddDefaultBin(SampledCoverpoint& point, const BinsOrOptions& bins) {
  CoverBin bin;
  bin.name = std::string(bins.name);
  bin.kind = CoverBinKind::kDefault;
  AddGuardedBin(point, bins, std::move(bin));
}

void AddIntegralBins(const CovergroupInstance& inst, SampledCoverpoint& point,
                     const BinsOrOptions& bins, SimContext& ctx, Arena& arena) {
  switch (bins.kind) {
    case BinsOrOptionsKind::kValues:
    case BinsOrOptionsKind::kCoverPointWith:
      AddRangeListBins(inst, point, bins, ctx, arena);
      return;
    case BinsOrOptionsKind::kSetExpression:
      AddValueBins(point, bins,
                   {SetExpressionValues(bins.set_expr, ctx, arena), nullptr},
                   ctx, arena);
      return;
    case BinsOrOptionsKind::kTransitions:
      AddTransitionBins(point, bins, ctx, arena);
      return;
    case BinsOrOptionsKind::kDefault:
      AddDefaultBin(point, bins);
      return;
    default:
      return;
  }
}

}  // namespace

std::vector<CoverValueRange> CovergroupRangeValues(
    const std::vector<CovergroupValueRange>& ranges,
    const SampledCoverpoint& point, SimContext& ctx, Arena& arena) {
  return ReadRangeList(ranges, false, point, ctx, arena);
}

void BuildCoverpointBins(CovergroupInstance& inst, SampledCoverpoint& point,
                         const CoverPointDecl& decl, SimContext& ctx,
                         Arena& arena) {
  CoverPoint* cp = point.point;
  cp->is_real = point.is_real;
  for (const BinsOrOptions& bins : decl.bins) {
    if (point.is_real && bins.kind == BinsOrOptionsKind::kValues) {
      AddRealBins(point, bins, ctx, arena);
    } else if (bins.kind == BinsOrOptionsKind::kDefault) {
      AddDefaultBin(point, bins);
    } else if (!point.is_real) {
      AddIntegralBins(inst, point, bins, ctx, arena);
    }
  }
  CoverValueRange bounds = PointTypeBounds(point);
  CoverageDB::AutoCreateBins(cp, bounds.lo, bounds.hi);
  ExcludeIgnoredAndIllegalValues(cp);
  for (CoverBin& bin : cp->bins) {
    bin.at_least = static_cast<uint32_t>(std::max(0, point.option.at_least));
  }
}

}  // namespace delta
