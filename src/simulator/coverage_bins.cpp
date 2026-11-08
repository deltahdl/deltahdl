#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

namespace delta {

std::string CoverageDB::StateBinName(std::string_view base, int64_t index) {
  return std::string(base) + "[" + std::to_string(index) + "]";
}

std::vector<CoverBin> CoverageDB::OpenArrayValueBins(
    std::string_view base, const std::vector<int64_t>& values) {
  std::vector<CoverBin> bins;
  for (int64_t value : values) {
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
  if (uses_dollar) {
    result.push_back({low, high, true});
    return result;
  }
  constexpr double kEps = 1e-9;
  double width = high - low;
  if (interval <= 0.0 || width <= interval + kEps) {
    result.push_back({low, high, true});
    return result;
  }
  int count = static_cast<int>(std::ceil(width / interval - kEps));
  if (count < 1) count = 1;
  for (int i = 0; i < count; ++i) {
    bool last = (i == count - 1);
    double lo = low + static_cast<double>(i) * interval;
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

std::pair<double, double> CoverageDB::ToleranceRange(double value,
                                                     double tolerance,
                                                     bool is_percent) {
  double delta = is_percent ? std::fabs(value) * tolerance / 100.0 : tolerance;
  if (delta < 0.0) delta = -delta;
  return {value - delta, value + delta};
}

std::vector<int64_t> CoverageDB::ApplyWithExpression(
    const std::vector<int64_t>& candidates,
    const std::function<bool(int64_t)>& pred) {
  std::vector<int64_t> selected;
  for (int64_t value : candidates) {
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
    return DistributeValues(ApplyWithExpression(candidates, pred), num_bins);
  }
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

uint64_t CoverageDB::SetExpressionEvaluationCount(uint64_t) { return 1; }

bool CoverageDB::TransitionBinAllowed(const CoverPoint* cp) {
  return !cp->is_real;
}

bool CoverageDB::TransitionLengthLegal(size_t sample_points) {
  return sample_points >= 2;
}

std::vector<std::vector<int64_t>> CoverageDB::ExpandSetTransition(
    const std::vector<std::vector<int64_t>>& steps) {
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
  return kind == TransitionRepeatKind::kConsecutive;
}

bool CoverageDB::MultipleBinsAllowsTransition(bool sequence_bounded) {
  return sequence_bounded;
}

bool CoverageDB::DefaultSequenceAllowsMultipleBins() { return false; }

bool CoverageDB::DefaultSequenceTransitionIncrements(
    bool any_nondefault_incremented, bool any_pending) {
  return !any_nondefault_incremented && !any_pending;
}

std::vector<int64_t> CoverageDB::ExpandWildcardValue(int64_t pattern,
                                                     uint64_t care_mask,
                                                     uint32_t width) {
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
  return !sample_has_xz;
}

bool CoverageDB::WildcardBinsAllowed(const CoverPoint* cp) {
  return !cp->is_real;
}

std::vector<int64_t> CoverageDB::RemoveIgnoredValues(
    const std::vector<int64_t>& bin_values,
    const std::vector<int64_t>& ignored_values) {
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

bool CoverageDB::IgnoredValueAffectsTransition(int64_t,
                                               const std::vector<int64_t>&) {
  return false;
}

bool CoverageDB::IgnoreTransitionLengthLegal(bool sequence_bounded) {
  return sequence_bounded;
}

std::vector<int64_t> CoverageDB::RemoveIllegalValues(
    const std::vector<int64_t>& bin_values,
    const std::vector<int64_t>& illegal_values) {
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

bool CoverageDB::IllegalValueAffectsTransition(int64_t,
                                               const std::vector<int64_t>&) {
  return false;
}

bool CoverageDB::IllegalTransitionLengthLegal(bool sequence_bounded) {
  return sequence_bounded;
}

bool CoverageDB::IllegalTakesPrecedence(bool) { return true; }

CoverpointEffectiveType CoverageDB::EffectiveCoverpointType(
    bool has_coverpoint_type, CoverpointEffectiveType coverpoint_type,
    CoverpointEffectiveType self_determined_type) {
  return has_coverpoint_type ? coverpoint_type : self_determined_type;
}

int64_t CoverageDB::CastToEffectiveType(int64_t value,
                                        CoverpointEffectiveType eff) {
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
  if (value_has_xz && !is_wildcard) return BinValueResolution::kUnknownBits;
  if (!eff.is_signed && value_is_signed && value < 0)
    return BinValueResolution::kUnsignedNegative;
  bool fits = value_is_signed && eff.is_signed
                  ? CastToEffectiveType(value, eff) == value
                  : value >= 0 && value <= EffectiveTypeMax({eff.width, false});
  if (!fits) return BinValueResolution::kValueChanged;
  return BinValueResolution::kOk;
}

bool CoverageDB::SingletonValueParticipates(BinValueResolution resolution) {
  return resolution == BinValueResolution::kOk;
}

static std::vector<int64_t> EnumerateInclusiveRange(int64_t lo, int64_t hi) {
  std::vector<int64_t> out;
  for (int64_t v = lo;; ++v) {
    out.push_back(v);
    if (v == hi) break;
  }
  return out;
}

std::vector<int64_t> CoverageDB::ResolveBinRange(const BinRangeSpec& range,
                                                 CoverpointEffectiveType eff) {
  if (!range.is_wildcard && (range.low_has_xz || range.high_has_xz)) return {};
  if (range.low > range.high) return {};
  int64_t lo = std::max(range.low, EffectiveTypeMin(eff));
  int64_t hi = std::min(range.high, EffectiveTypeMax(eff));
  if (lo > hi) return {};
  return EnumerateInclusiveRange(lo, hi);
}

}  // namespace delta
