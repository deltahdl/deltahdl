#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/coverage.h"

namespace delta {

// --- LRM 19.5.1: specifying bins for values ---------------------------------

std::string CoverageDB::StateBinName(std::string_view base, int64_t index) {
  return std::string(base) + "[" + std::to_string(index) + "]";
}

std::vector<CoverBin> CoverageDB::OpenArrayValueBins(
    std::string_view base, const std::vector<int64_t>& values) {
  std::vector<CoverBin> bins;
  for (int64_t value : values) {
    // A value already given a bin is not given another, so overlapping ranges
    // collapse to one bin per distinct value (LRM 19.5.1).
    bool seen = false;
    for (const auto& existing : bins) {
      if (!existing.values.empty() && existing.values.front() == value) {
        seen = true;
        break;
      }
    }
    if (seen) continue;
    CoverBin bin;
    bin.name = StateBinName(base, value);
    bin.kind = CoverBinKind::kExplicit;
    bin.values = {value};
    bins.push_back(std::move(bin));
  }
  return bins;
}

// Renders a real value the way coverage bin names present it: a plain decimal
// that always shows a fractional point (e.g. 1.0, 0.75, -100.1).
static std::string FormatReal(double value) {
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%g", value);
  std::string text(buf);
  if (text.find('.') == std::string::npos &&
      text.find('e') == std::string::npos &&
      text.find('n') == std::string::npos) {
    text += ".0";
  }
  return text;
}

std::vector<RealInterval> CoverageDB::RealRangeIntervals(double low,
                                                         double high,
                                                         double interval,
                                                         bool uses_dollar) {
  std::vector<RealInterval> result;
  // A range bounded by the $ primary is assigned to a single bin and is never
  // divided into intervals (LRM 19.5.1).
  if (uses_dollar) {
    result.push_back({low, high, true});
    return result;
  }
  constexpr double kEps = 1e-9;
  double width = high - low;
  // A range no wider than one interval becomes a single interval, inclusive of
  // both endpoints (LRM 19.5.1).
  if (interval <= 0.0 || width <= interval + kEps) {
    result.push_back({low, high, true});
    return result;
  }
  int count = static_cast<int>(std::ceil(width / interval - kEps));
  if (count < 1) count = 1;
  for (int i = 0; i < count; ++i) {
    bool last = (i == count - 1);
    double lo = low + static_cast<double>(i) * interval;
    // The last partition runs to the range's high value (it may be shorter than
    // the interval) and is the only one inclusive of its high value
    // (LRM 19.5.1).
    double hi = last ? high : low + static_cast<double>(i + 1) * interval;
    result.push_back({lo, hi, last});
  }
  return result;
}

std::string CoverageDB::RealIntervalBinName(std::string_view base,
                                            const RealInterval& interval) {
  return std::string(base) + "[" + FormatReal(interval.low) + ":" +
         FormatReal(interval.high) + (interval.high_inclusive ? "]" : ")");
}

std::string CoverageDB::RealValueBinName(std::string_view base, double value) {
  return std::string(base) + "[" + FormatReal(value) + "]";
}

static bool IntervalsIdentical(const RealInterval& a, const RealInterval& b) {
  constexpr double kEps = 1e-9;
  return std::fabs(a.low - b.low) < kEps && std::fabs(a.high - b.high) < kEps &&
         a.high_inclusive == b.high_inclusive;
}

std::vector<RealInterval> CoverageDB::MergeIdenticalIntervals(
    const std::vector<RealInterval>& intervals) {
  std::vector<RealInterval> merged;
  for (const auto& iv : intervals) {
    bool duplicate = false;
    for (const auto& kept : merged) {
      if (IntervalsIdentical(iv, kept)) {
        duplicate = true;
        break;
      }
    }
    if (!duplicate) merged.push_back(iv);
  }
  return merged;
}

bool CoverageDB::RealDefaultBinMayBeArray() { return false; }

// --- LRM 19.5.1.1: coverpoint bin "with" expressions ------------------------

std::vector<int64_t> CoverageDB::ApplyWithExpression(
    const std::vector<int64_t>& candidates,
    const std::function<bool(int64_t)>& pred) {
  std::vector<int64_t> selected;
  for (int64_t value : candidates) {
    // "item" is the candidate value; matching values keep their original order
    // and any duplicates are retained (LRM 19.5.1.1).
    if (pred(value)) selected.push_back(value);
  }
  return selected;
}

std::vector<std::vector<int64_t>> CoverageDB::DistributeValues(
    const std::vector<int64_t>& values, uint32_t num_bins) {
  std::vector<std::vector<int64_t>> bins;
  if (num_bins == 0) return bins;
  bins.resize(num_bins);
  auto total = static_cast<int64_t>(values.size());
  int64_t per_bin = total / static_cast<int64_t>(num_bins);
  if (per_bin < 1) per_bin = 1;
  size_t cursor = 0;
  for (uint32_t i = 0; i < num_bins && cursor < values.size(); ++i) {
    int64_t take = per_bin;
    // The last bin absorbs whatever values remain (LRM 19.5.1).
    if (i + 1 == num_bins) take = total - static_cast<int64_t>(cursor);
    for (int64_t j = 0; j < take && cursor < values.size(); ++j) {
      bins[i].push_back(values[cursor++]);
    }
  }
  return bins;
}

std::vector<std::vector<int64_t>> CoverageDB::ApplyWithAndDistribute(
    const std::vector<int64_t>& candidates,
    const std::function<bool(int64_t)>& pred, uint32_t num_bins,
    bool distribute_first) {
  if (!distribute_first) {
    // Default order: filter the candidate set, then distribute the survivors.
    return DistributeValues(ApplyWithExpression(candidates, pred), num_bins);
  }
  // distribute_first: distribute first, then filter the contents of each bin
  // (LRM 19.5.1.1, LRM 19.7.1).
  std::vector<std::vector<int64_t>> distributed =
      DistributeValues(candidates, num_bins);
  for (auto& bin : distributed) {
    bin = ApplyWithExpression(bin, pred);
  }
  return distributed;
}

bool CoverageDB::WithExpressionAllowed(const CoverPoint* cp) {
  return !cp->is_real;
}

bool CoverageDB::WithRangeReferenceAllowed(std::string_view self_name,
                                           std::string_view referenced_name) {
  return self_name == referenced_name;
}

// --- LRM 19.5.1.2: coverpoint bin set covergroup expressions ----------------

uint64_t CoverageDB::SetExpressionEvaluationCount(uint64_t /*sample_count*/) {
  // The set_covergroup_expression is evaluated once, at construction of the
  // covergroup instance, not at each sampling point (LRM 19.5.1.2).
  return 1;
}

// --- LRM 19.5.2: specifying bins for transitions ----------------------------

bool CoverageDB::TransitionBinAllowed(const CoverPoint* cp) {
  // Transition bins of real values are not allowed (LRM 19.5.2).
  return !cp->is_real;
}

bool CoverageDB::TransitionLengthLegal(size_t sample_points) {
  // A length-0 transition specification (one sample point, no transition) is
  // illegal; a valid transition spans at least two successive points
  // (LRM 19.5.2).
  return sample_points >= 2;
}

std::vector<std::vector<int64_t>> CoverageDB::ExpandSetTransition(
    const std::vector<std::vector<int64_t>>& steps) {
  // The set transition expands to every ordered combination that picks one
  // value from each step in turn (LRM 19.5.2).
  std::vector<std::vector<int64_t>> result;
  if (steps.empty()) return result;
  result.push_back({});
  for (const auto& step : steps) {
    std::vector<std::vector<int64_t>> next;
    for (const auto& prefix : result) {
      for (int64_t value : step) {
        std::vector<int64_t> seq = prefix;
        seq.push_back(value);
        next.push_back(std::move(seq));
      }
    }
    result = std::move(next);
  }
  return result;
}

std::vector<std::vector<int64_t>> CoverageDB::ExpandConsecutiveRepeat(
    const std::vector<int64_t>& item, uint32_t lo, uint32_t hi) {
  // For each repetition count in [lo, hi] the item's values are concatenated
  // that many times, yielding one concrete sequence per count (LRM 19.5.2).
  std::vector<std::vector<int64_t>> result;
  if (hi < lo) return result;
  for (uint32_t n = lo; n <= hi; ++n) {
    std::vector<int64_t> seq;
    seq.reserve(item.size() * n);
    for (uint32_t r = 0; r < n; ++r) {
      seq.insert(seq.end(), item.begin(), item.end());
    }
    result.push_back(std::move(seq));
  }
  return result;
}

std::string CoverageDB::TransitionArrayBinName(
    std::string_view base, const std::vector<int64_t>& transition) {
  std::string name(base);
  name += "[";
  for (size_t i = 0; i < transition.size(); ++i) {
    if (i != 0) name += "=>";
    name += std::to_string(transition[i]);
  }
  name += "]";
  return name;
}

bool CoverageDB::TransitionRepeatBounded(TransitionRepeatKind kind) {
  // Consecutive repetition has a determined length; the goto and nonconsecutive
  // forms can vary in length and are unbounded (LRM 19.5.2).
  return kind == TransitionRepeatKind::kConsecutive;
}

bool CoverageDB::MultipleBinsAllowsTransition(bool sequence_bounded) {
  // The "[]" notation requires a bounded transition; an unbounded sequence with
  // it is an error (LRM 19.5.2).
  return sequence_bounded;
}

bool CoverageDB::DefaultSequenceAllowsMultipleBins() { return false; }

bool CoverageDB::DefaultSequenceTransitionIncrements(
    bool any_nondefault_incremented, bool any_pending) {
  // The default sequence bin counts only when no other transition bin fired on
  // this sample and nothing remains pending (LRM 19.5.2).
  return !any_nondefault_incremented && !any_pending;
}

// --- LRM 19.5.4: wildcard specification of coverage point bins ---------------

std::vector<int64_t> CoverageDB::ExpandWildcardValue(int64_t pattern,
                                                     uint64_t care_mask,
                                                     uint32_t width) {
  // Each wildcard (x, z, or ?) bit matches both 0 and 1, while the fixed bits
  // must match exactly; the matching set is therefore every value formed by
  // filling the wildcard positions with all combinations of 0 and 1, so a
  // single wildcard bin covers a contiguous group such as 12..15 for 4'b11??
  // (LRM 19.5.4).
  if (width == 0 || width > 63) return {};
  uint64_t width_mask = (uint64_t{1} << width) - 1;
  uint64_t fixed = static_cast<uint64_t>(pattern) & care_mask & width_mask;
  std::vector<uint32_t> wild_positions;
  for (uint32_t b = 0; b < width; ++b) {
    if ((care_mask & (uint64_t{1} << b)) == 0) wild_positions.push_back(b);
  }
  std::vector<int64_t> out;
  uint64_t combos = uint64_t{1} << wild_positions.size();
  out.reserve(combos);
  for (uint64_t c = 0; c < combos; ++c) {
    uint64_t v = fixed;
    for (size_t i = 0; i < wild_positions.size(); ++i) {
      if (c & (uint64_t{1} << i)) v |= (uint64_t{1} << wild_positions[i]);
    }
    out.push_back(static_cast<int64_t>(v));
  }
  return out;
}

bool CoverageDB::WildcardSampleIncluded(bool sample_has_xz) {
  // A wildcard bin considers 2-state values only; a sample carrying x or z is
  // excluded from the comparison (LRM 19.5.4).
  return !sample_has_xz;
}

bool CoverageDB::WildcardBinsAllowed(const CoverPoint* cp) {
  // Wildcard bins may not be specified for a real coverpoint (LRM 19.5.4).
  return !cp->is_real;
}

// --- LRM 19.5.5: excluding coverage point values or transitions -------------

std::vector<int64_t> CoverageDB::RemoveIgnoredValues(
    const std::vector<int64_t>& bin_values,
    const std::vector<int64_t>& ignored_values) {
  // Each ignored value is removed from the bin's set of values; the rest keep
  // their relative order (LRM 19.5.5).
  std::vector<int64_t> result;
  result.reserve(bin_values.size());
  for (int64_t value : bin_values) {
    bool ignored = false;
    for (int64_t ig : ignored_values) {
      if (ig == value) {
        ignored = true;
        break;
      }
    }
    if (!ignored) result.push_back(value);
  }
  return result;
}

bool CoverageDB::CoveredTransitionIsIgnored(
    const std::vector<int64_t>& covered, const std::vector<int64_t>& ignored) {
  // The covered sequence is removed when the ignored sequence appears within it
  // contiguously: every occurrence of the covered sequence then necessarily
  // matches the ignored one as well (LRM 19.5.5).
  if (ignored.empty()) return false;
  if (ignored.size() > covered.size()) return false;
  for (size_t start = 0; start + ignored.size() <= covered.size(); ++start) {
    bool match = true;
    for (size_t i = 0; i < ignored.size(); ++i) {
      if (covered[start + i] != ignored[i]) {
        match = false;
        break;
      }
    }
    if (match) return true;
  }
  return false;
}

bool CoverageDB::IgnoredValueAffectsTransition(
    int64_t /*ignored_value*/, const std::vector<int64_t>& /*transition*/) {
  // Ignoring a single value never removes a transition that passes through it
  // (LRM 19.5.5).
  return false;
}

bool CoverageDB::IgnoreTransitionLengthLegal(bool sequence_bounded) {
  // An ignored transition sequence of unbounded or undetermined length is
  // illegal; only a bounded sequence is allowed (LRM 19.5.5).
  return sequence_bounded;
}

// --- LRM 19.5.6: specifying illegal coverage point values or transitions ----

std::vector<int64_t> CoverageDB::RemoveIllegalValues(
    const std::vector<int64_t>& bin_values,
    const std::vector<int64_t>& illegal_values) {
  // Each illegal value is removed from the bin's set of values; the surviving
  // values keep their relative order (LRM 19.5.6).
  std::vector<int64_t> result;
  result.reserve(bin_values.size());
  for (int64_t value : bin_values) {
    bool illegal = false;
    for (int64_t bad : illegal_values) {
      if (bad == value) {
        illegal = true;
        break;
      }
    }
    if (!illegal) result.push_back(value);
  }
  return result;
}

bool CoverageDB::CoveredTransitionIsIllegal(
    const std::vector<int64_t>& covered, const std::vector<int64_t>& illegal) {
  // The covered sequence is removed when the illegal sequence appears within it
  // contiguously: every occurrence of the covered sequence then necessarily
  // matches the illegal one as well (LRM 19.5.6).
  if (illegal.empty()) return false;
  if (illegal.size() > covered.size()) return false;
  for (size_t start = 0; start + illegal.size() <= covered.size(); ++start) {
    bool match = true;
    for (size_t i = 0; i < illegal.size(); ++i) {
      if (covered[start + i] != illegal[i]) {
        match = false;
        break;
      }
    }
    if (match) return true;
  }
  return false;
}

bool CoverageDB::IllegalValueAffectsTransition(
    int64_t /*illegal_value*/, const std::vector<int64_t>& /*transition*/) {
  // Specifying a single illegal value never removes a transition that passes
  // through it (LRM 19.5.6).
  return false;
}

bool CoverageDB::IllegalTransitionLengthLegal(bool sequence_bounded) {
  // An illegal transition sequence of unbounded or undetermined length is not
  // allowed; only a bounded sequence is legal (LRM 19.5.6).
  return sequence_bounded;
}

bool CoverageDB::IllegalTakesPrecedence(bool /*also_in_other_bin*/) {
  // An illegal bin always wins: hitting it raises a run-time error regardless
  // of whether the value or transition also belongs to another bin
  // (LRM 19.5.6).
  return true;
}

// --- LRM 19.5.7: value resolution -------------------------------------------

CoverpointEffectiveType CoverageDB::EffectiveCoverpointType(
    bool has_coverpoint_type, CoverpointEffectiveType coverpoint_type,
    CoverpointEffectiveType self_determined_type) {
  // The coverpoint type, when present, governs the comparison; otherwise the
  // expression resolves its own type (LRM 19.5.7 a).
  return has_coverpoint_type ? coverpoint_type : self_determined_type;
}

int64_t CoverageDB::CastToEffectiveType(int64_t value,
                                        CoverpointEffectiveType eff) {
  // Keep only the low `width` bits, then sign-extend for a signed type so the
  // cast matches a normal static cast to the effective type (LRM 19.5.7 b).
  if (eff.width == 0) return 0;
  if (eff.width >= 64) return value;
  uint64_t mask = (uint64_t{1} << eff.width) - 1;
  uint64_t bits = static_cast<uint64_t>(value) & mask;
  if (eff.is_signed && (bits & (uint64_t{1} << (eff.width - 1)))) bits |= ~mask;
  return static_cast<int64_t>(bits);
}

int64_t CoverageDB::EffectiveTypeMin(CoverpointEffectiveType eff) {
  if (eff.width == 0 || !eff.is_signed) return 0;
  if (eff.width >= 64) return INT64_MIN;
  return -(int64_t{1} << (eff.width - 1));
}

int64_t CoverageDB::EffectiveTypeMax(CoverpointEffectiveType eff) {
  if (eff.width == 0) return 0;
  if (eff.width >= 64) return INT64_MAX;
  if (eff.is_signed) return (int64_t{1} << (eff.width - 1)) - 1;
  return (int64_t{1} << eff.width) - 1;
}

BinValueResolution CoverageDB::ResolveBinValue(int64_t value,
                                               bool value_is_signed,
                                               bool value_has_xz,
                                               bool is_wildcard,
                                               CoverpointEffectiveType eff) {
  // Condition 3: a value with x or z bits warns, except for a wildcard bin
  // whose unknown bits were resolved to 0/1 beforehand (LRM 19.5.7 preamble,
  // condition 3).
  if (value_has_xz && !is_wildcard) return BinValueResolution::kUnknownBits;
  // Condition 1: a negative signed value assigned to an unsigned effective
  // type (LRM 19.5.7 b, condition 1).
  if (!eff.is_signed && value_is_signed && value < 0)
    return BinValueResolution::kUnsignedNegative;
  // Condition 2: the static cast to the effective type alters the value, i.e.
  // the value is not expressible in that type (LRM 19.5.7 b, condition 2).
  if (CastToEffectiveType(value, eff) != value)
    return BinValueResolution::kValueChanged;
  return BinValueResolution::kOk;
}

bool CoverageDB::SingletonValueParticipates(BinValueResolution resolution) {
  // A singleton that triggers a warning is removed from the bin's values
  // (LRM 19.5.7, first warning bullet).
  return resolution == BinValueResolution::kOk;
}

// Enumerates every integer in [lo, hi] inclusive. The loop terminates on the
// high value rather than on an exhausted increment so it stays safe when
// hi == INT64_MAX (LRM 19.5.7, second and third range bullets).
static std::vector<int64_t> EnumerateInclusiveRange(int64_t lo, int64_t hi) {
  std::vector<int64_t> out;
  for (int64_t v = lo;; ++v) {
    out.push_back(v);
    if (v == hi) break;
  }
  return out;
}

std::vector<int64_t> CoverageDB::ResolveBinRange(int64_t low, int64_t high,
                                                 bool low_has_xz,
                                                 bool high_has_xz,
                                                 bool is_wildcard,
                                                 CoverpointEffectiveType eff) {
  // An x/z bit in either endpoint removes the whole range, unless this is a
  // wildcard bin whose unknown bits were already resolved (LRM 19.5.7, second
  // range bullet).
  if (!is_wildcard && (low_has_xz || high_has_xz)) return {};
  if (low > high) return {};
  // The surviving range is the intersection of [low:high] with the domain the
  // effective type can express. An empty intersection means every value in the
  // range would warn, so the range drops out (LRM 19.5.7, second and third
  // range bullets).
  int64_t lo = std::max(low, EffectiveTypeMin(eff));
  int64_t hi = std::min(high, EffectiveTypeMax(eff));
  if (lo > hi) return {};
  return EnumerateInclusiveRange(lo, hi);
}

}  // namespace delta
