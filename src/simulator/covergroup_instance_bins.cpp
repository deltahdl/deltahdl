#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
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

using ValueList = std::vector<CoverValueRange>;

constexpr uint64_t kAllValues = std::numeric_limits<uint64_t>::max();

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

void AppendValue(ValueList& list, int64_t v) {
  if (!list.empty() && list.back().hi != std::numeric_limits<int64_t>::max() &&
      list.back().hi + 1 == v) {
    list.back().hi = v;
    return;
  }
  list.push_back({v, v});
}

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

CoverpointEffectiveType EffectiveTypeOf(const SampledCoverpoint& point) {
  if (point.width == 0 || point.width >= 64) {
    return {64, point.width == 0 || point.is_signed};
  }
  return {point.width, point.is_signed};
}

void WarnOfBinValue(SourceLoc at, int64_t value, BinValueResolution resolution,
                    DiagEngine& diag) {
  std::string message;
  if (resolution == BinValueResolution::kUnknownBits) {
    message = "a bin value holding x or z bits takes no part in its bin";
  } else if (resolution == BinValueResolution::kUnsignedNegative) {
    message = std::format(
        "bin value {} is negative while the coverpoint's type is unsigned, "
        "and takes no part in its bin",
        value);
  } else {
    message = std::format(
        "bin value {} does not fit the coverpoint's type and takes no part in "
        "its bin",
        value);
  }
  diag.Warning(at, message, Subclause("19.5.7"));
}

std::optional<int64_t> ResolvedValue(const Logic4Vec& value, SourceLoc at,
                                     const SampledCoverpoint& point,
                                     DiagEngine& diag) {
  int64_t v = CovergroupIntOf(value);
  BinValueResolution resolution = CoverageDB::ResolveBinValue(
      v, value.is_signed, !value.IsKnown(), false, EffectiveTypeOf(point));
  if (!CoverageDB::SingletonValueParticipates(resolution)) {
    WarnOfBinValue(at, v, resolution, diag);
    return std::nullopt;
  }
  return CoverageDB::CastToEffectiveType(v, EffectiveTypeOf(point));
}

void AppendSingleton(const CovergroupValueRange& range,
                     const SampledCoverpoint& point, SimContext& ctx,
                     Arena& arena, ValueList& out) {
  if (std::optional<int64_t> held =
          ResolvedValue(EvalExpr(range.lo, ctx, arena), range.lo->range.start,
                        point, ctx.GetDiag())) {
    out.push_back({*held, *held});
  }
}

CoverValueRange ExpressedValues(const SampledCoverpoint& point,
                                bool unsigned_bounds) {
  CoverpointEffectiveType eff = EffectiveTypeOf(point);
  if (!unsigned_bounds || !eff.is_signed || eff.width >= 64) {
    return PointTypeBounds(point);
  }
  return {0, CoverageDB::EffectiveTypeMax({eff.width, false})};
}

void AppendAsHeld(CoverValueRange kept, const SampledCoverpoint& point,
                  ValueList& out) {
  CoverpointEffectiveType eff = EffectiveTypeOf(point);
  int64_t top = CoverageDB::EffectiveTypeMax(eff);
  if (kept.hi <= top) {
    out.push_back(kept);
    return;
  }
  if (kept.lo <= top) out.push_back({kept.lo, top});
  out.push_back(
      {CoverageDB::CastToEffectiveType(std::max(kept.lo, top + 1), eff),
       CoverageDB::CastToEffectiveType(kept.hi, eff)});
}

void AppendRange(const CovergroupValueRange& range,
                 const SampledCoverpoint& point, SimContext& ctx, Arena& arena,
                 ValueList& out) {
  const Expr* at = range.lo != nullptr ? range.lo : range.hi;
  CoverValueRange written = PointTypeBounds(point);
  bool unsigned_bounds = false;
  for (auto [bound, end] :
       {std::pair{range.lo, &written.lo}, std::pair{range.hi, &written.hi}}) {
    if (bound == nullptr) continue;
    Logic4Vec value = EvalExpr(bound, ctx, arena);
    if (!value.IsKnown()) {
      ctx.GetDiag().Warning(at->range.start,
                            "a bin range with an x or z bound takes no part "
                            "in its bin",
                            Subclause("19.5.7"));
      return;
    }
    *end = CovergroupIntOf(value);
    unsigned_bounds = unsigned_bounds || !value.is_signed;
  }
  if (written.lo > written.hi) return;
  CoverValueRange domain = ExpressedValues(point, unsigned_bounds);
  CoverValueRange kept{std::max(written.lo, domain.lo),
                       std::min(written.hi, domain.hi)};
  if (kept.lo > kept.hi) {
    ctx.GetDiag().Warning(
        at->range.start,
        std::format("bin range [{}:{}] holds no value the coverpoint's type "
                    "can express and takes no part in its bin",
                    written.lo, written.hi),
        Subclause("19.5.7"));
    return;
  }
  if (kept.lo != written.lo || kept.hi != written.hi) {
    ctx.GetDiag().Warning(
        at->range.start,
        std::format("bin range [{}:{}] holds values the coverpoint's type "
                    "cannot express; only [{}:{}] takes part in its bin",
                    written.lo, written.hi, kept.lo, kept.hi),
        Subclause("19.5.7"));
  }
  AppendAsHeld(kept, point, out);
}

void AppendValueRange(const CovergroupValueRange& range,
                      const SampledCoverpoint& point, SimContext& ctx,
                      Arena& arena, ValueList& out) {
  if (range.kind == CovergroupValueRangeKind::kValue) {
    AppendSingleton(range, point, ctx, arena, out);
    return;
  }
  if (range.kind == CovergroupValueRangeKind::kRange) {
    AppendRange(range, point, ctx, arena, out);
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

ValueList SetExpressionValues(const Expr* e, const SampledCoverpoint& point,
                              SimContext& ctx, Arena& arena) {
  ValueList values;
  if (e->kind != ExprKind::kIdentifier) return values;
  std::vector<Logic4Vec> elements;
  if (const ArrayInfo* info = ctx.FindArrayInfo(e->text)) {
    elements = CollectVecElements(e->text, *info, ctx, arena);
  } else if (const QueueObject* queue = ctx.FindQueue(e->text)) {
    elements = queue->elements;
  }
  for (const Logic4Vec& element : elements) {
    if (std::optional<int64_t> held =
            ResolvedValue(element, e->range.start, point, ctx.GetDiag())) {
      AppendValue(values, *held);
    }
  }
  return values;
}

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

void AddGuardedBin(SampledCoverpoint& point, const BinsOrOptions& bins,
                   CoverBin bin) {
  size_t index = point.point->bins.size();
  CoverageDB::AddBin(point.point, std::move(bin));
  if (bins.iff != nullptr) point.bin_guards.emplace_back(index, bins.iff);
}

std::optional<uint64_t> BinArraySize(const BinsOrOptions& bins, SimContext& ctx,
                                     Arena& arena) {
  int64_t size = CovergroupInt(bins.array_size, ctx, arena);
  if (size > 0) return static_cast<uint64_t>(size);
  ctx.GetDiag().Error(
      bins.array_size->range.start,
      std::format("bins '{}' asks for {} bins; the number of bins is a "
                  "positive integral value",
                  bins.name, size),
      Subclause("19.5.1"));
  return std::nullopt;
}

struct BinValues {
  ValueList values;
  const Expr* with_each = nullptr;
};

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
  std::optional<uint64_t> size = BinArraySize(bins, ctx, arena);
  if (!size.has_value()) return;
  uint64_t count = *size;
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

TransitionPatternElement PatternElement(const TransStep& step) {
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
  return element;
}

std::vector<std::vector<TransitionPatternElement>> TransSetPatterns(
    const std::vector<TransStep>& steps) {
  std::vector<std::vector<TransitionPatternElement>> patterns = {{}};
  for (const TransStep& step : steps) {
    TransitionPatternElement element = PatternElement(step);
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

bool IsExcludingBin(const CoverBin& bin) {
  return bin.kind == CoverBinKind::kIgnore ||
         bin.kind == CoverBinKind::kIllegal;
}

void ExcludeIgnoredAndIllegalValues(CoverPoint* cp) {
  ValueList excluded;
  for (const CoverBin& bin : cp->bins) {
    if (!IsExcludingBin(bin)) continue;
    for (int64_t v : bin.values) excluded.push_back({v, v});
    excluded.insert(excluded.end(), bin.ranges.begin(), bin.ranges.end());
  }
  if (excluded.empty()) return;
  excluded = NormalizeSpans(std::move(excluded));
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

void ExcludeIgnoredAndIllegalTransitions(CoverPoint* cp) {
  std::set<std::vector<int64_t>> excluded;
  for (const CoverBin& bin : cp->bins) {
    if (IsExcludingBin(bin))
      excluded.insert(bin.transitions.begin(), bin.transitions.end());
  }
  if (excluded.empty()) return;
  auto holds_excluded = [&excluded](const std::vector<int64_t>& sequence) {
    return std::ranges::any_of(excluded, [&sequence](const auto& run) {
      return !std::ranges::search(sequence, run).empty();
    });
  };
  for (CoverBin& bin : cp->bins) {
    if (bin.kind != CoverBinKind::kTransition) continue;
    std::erase_if(bin.transitions, holds_excluded);
  }
}

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

void AddRealBinArray(SampledCoverpoint& point, const BinsOrOptions& bins,
                     const std::vector<RealItem>& parts, SimContext& ctx,
                     Arena& arena) {
  std::optional<uint64_t> size = BinArraySize(bins, ctx, arena);
  if (!size.has_value()) return;
  auto count = static_cast<size_t>(*size);
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

void AddDefaultBin(SampledCoverpoint& point, const BinsOrOptions& bins,
                   CoverBinKind kind) {
  CoverBin bin;
  bin.name = std::string(bins.name);
  bin.kind = kind;
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
      AddValueBins(
          point, bins,
          {SetExpressionValues(bins.set_expr, point, ctx, arena), nullptr}, ctx,
          arena);
      return;
    case BinsOrOptionsKind::kTransitions:
      AddTransitionBins(point, bins, ctx, arena);
      return;
    case BinsOrOptionsKind::kDefaultSequence:
      AddDefaultBin(point, bins, CoverBinKind::kDefaultSequence);
      return;
    default:
      return;
  }
}

std::vector<std::pair<std::string_view, int64_t>> EnumMembers(
    const SampledCoverpoint& point) {
  std::vector<std::pair<std::string_view, int64_t>> members;
  for (const EnumMemberInfo& member : point.enum_type->members) {
    if (member.xz == 0) {
      members.emplace_back(member.name,
                           ConvertToPointType(member.value, point));
    }
  }
  return members;
}

}  // namespace

std::vector<CoverValueRange> NormalizeSpans(std::vector<CoverValueRange> list) {
  std::ranges::sort(list, {}, &CoverValueRange::lo);
  std::vector<CoverValueRange> joined;
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
  std::vector<SourceLoc> origins;
  for (const BinsOrOptions& bins : decl.bins) {
    if (point.is_real && bins.kind == BinsOrOptionsKind::kValues) {
      AddRealBins(point, bins, ctx, arena);
    } else if (bins.kind == BinsOrOptionsKind::kDefault) {
      AddDefaultBin(point, bins, CoverBinKind::kDefault);
    } else if (!point.is_real) {
      AddIntegralBins(inst, point, bins, ctx, arena);
    }
    origins.resize(cp->bins.size(), bins.loc);
  }
  if (point.option.detect_overlap) {
    WarnOfBinOverlaps(*cp, origins, ctx.GetDiag());
  }
  if (point.enum_type != nullptr) {
    CoverageDB::AutoCreateEnumBins(cp, EnumMembers(point));
  } else {
    CoverValueRange bounds = PointTypeBounds(point);
    CoverageDB::AutoCreateBins(cp, bounds.lo, bounds.hi);
  }
  ExcludeIgnoredAndIllegalValues(cp);
  ExcludeIgnoredAndIllegalTransitions(cp);
  for (CoverBin& bin : cp->bins) {
    bin.at_least = static_cast<uint32_t>(std::max(0, point.option.at_least));
  }
}

}  // namespace delta
