#include "simulator/coverage.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/coverage_internal.h"
#include "simulator/coverage_types.h"

namespace delta {

static bool MatchesBinValues(const CoverBin& bin, int64_t value) {
  for (int64_t v : bin.values) {
    if (v == value) return true;
  }
  return std::ranges::any_of(bin.ranges, [&](const CoverValueRange& r) {
    return r.lo <= value && value <= r.hi;
  });
}

static bool MatchesBin(const CoverBin& bin, int64_t value) {
  if (bin.kind == CoverBinKind::kTransition) return false;
  return MatchesBinValues(bin, value);
}

static bool FindSampleValue(
    const std::vector<std::pair<std::string, int64_t>>& vals,
    const std::string& cp_name, int64_t& out) {
  for (const auto& [name, val] : vals) {
    if (name == cp_name) {
      out = val;
      return true;
    }
  }
  return false;
}

bool IsInValueSet(const std::vector<int64_t>& set, int64_t val) {
  for (int64_t v : set) {
    if (v == val) return true;
  }
  return false;
}

static bool MatchesCrossBin(
    const CrossBin& cbin, const std::vector<std::string>& cp_names,
    const std::vector<std::pair<std::string, int64_t>>& vals) {
  if (cbin.value_sets.size() != cp_names.size()) return false;
  for (size_t i = 0; i < cp_names.size(); ++i) {
    int64_t sample_val = 0;
    if (!FindSampleValue(vals, cp_names[i], sample_val)) return false;
    if (!IsInValueSet(cbin.value_sets[i], sample_val)) return false;
  }
  return true;
}

CoverGroup* CoverageDB::CreateGroup(std::string name) {
  size_t idx = groups_.size();
  CoverGroup group;
  group.name = std::move(name);
  groups_.push_back(std::move(group));
  name_index_[groups_[idx].name] = idx;
  return &groups_[idx];
}

CoverGroup* CoverageDB::FindGroup(std::string_view name) {
  auto it = name_index_.find(std::string(name));
  if (it == name_index_.end()) return nullptr;
  return &groups_[it->second];
}

uint32_t CoverageDB::GroupCount() const {
  return static_cast<uint32_t>(groups_.size());
}

CoverPoint* CoverageDB::AddCoverPoint(CoverGroup* group, std::string name) {
  CoverPoint cp;
  cp.name = std::move(name);
  cp.auto_bin_count = static_cast<uint32_t>(group->options.auto_bin_max);
  group->coverpoints.push_back(std::move(cp));
  return &group->coverpoints.back();
}

CoverBin* CoverageDB::AddBin(CoverPoint* cp, CoverBin bin) {
  cp->bins.push_back(std::move(bin));
  return &cp->bins.back();
}

bool CoverageDB::AutoBinsAllowed(const CoverPoint* cp) { return !cp->is_real; }

bool CoverageDB::ShouldAutoCreateBins(const CoverPoint* cp) {
  if (!AutoBinsAllowed(cp)) return false;
  for (const auto& bin : cp->bins) {
    if (bin.kind != CoverBinKind::kIgnore &&
        bin.kind != CoverBinKind::kIllegal && bin.kind != CoverBinKind::kAuto) {
      return false;
    }
  }
  return true;
}

uint64_t CoverageDB::AutoBinCount(uint32_t coverpoint_bits,
                                  uint64_t auto_bin_max) {
  uint64_t two_pow_m =
      coverpoint_bits >= 64 ? UINT64_MAX : (uint64_t{1} << coverpoint_bits);
  return std::min(two_pow_m, auto_bin_max);
}

uint64_t CoverageDB::AutoBinCountEnum(uint64_t enum_cardinality) {
  return enum_cardinality;
}

bool CoverageDB::AutoBinSampleIncluded(bool sample_has_xz) {
  return !sample_has_xz;
}

std::string CoverageDB::AutoBinName(int64_t low, int64_t high) {
  if (low == high) return "auto[" + std::to_string(low) + "]";
  return "auto[" + std::to_string(low) + ":" + std::to_string(high) + "]";
}

std::string CoverageDB::AutoEnumBinName(std::string_view constant_name) {
  return "auto[" + std::string(constant_name) + "]";
}

void CoverageDB::AutoCreateBins(CoverPoint* cp, int64_t min_val,
                                int64_t max_val) {
  if (!ShouldAutoCreateBins(cp)) return;
  cp->auto_bin_min = min_val;
  cp->auto_bin_max = max_val;
  if (max_val < min_val) return;
  uint64_t span =
      static_cast<uint64_t>(max_val) - static_cast<uint64_t>(min_val);
  uint64_t bin_count = cp->auto_bin_count;
  if (span < bin_count) bin_count = span + 1;
  if (bin_count == 0) return;

  uint64_t per_bin =
      (span / bin_count) + (span % bin_count == bin_count - 1 ? 1 : 0);
  auto cursor = static_cast<uint64_t>(min_val);
  for (uint64_t i = 0; i < bin_count; ++i) {
    auto low = static_cast<int64_t>(cursor);
    int64_t high = i + 1 == bin_count
                       ? max_val
                       : static_cast<int64_t>(cursor + per_bin - 1);
    CoverBin bin;
    bin.kind = CoverBinKind::kAuto;
    bin.name = AutoBinName(low, high);
    bin.ranges.push_back({low, high});
    cursor += per_bin;
    cp->bins.push_back(std::move(bin));
  }
}

void CoverageDB::AutoCreateEnumBins(
    CoverPoint* cp,
    const std::vector<std::pair<std::string_view, int64_t>>& members) {
  if (!ShouldAutoCreateBins(cp)) return;
  for (const auto& [name, value] : members) {
    CoverBin bin;
    bin.kind = CoverBinKind::kAuto;
    bin.name = AutoEnumBinName(name);
    bin.values.push_back(value);
    cp->bins.push_back(std::move(bin));
  }
}

CrossCover* CoverageDB::AddCross(CoverGroup* group, CrossCover cross) {
  group->crosses.push_back(std::move(cross));
  return &group->crosses.back();
}

template <typename Matches>
static bool ValueHitsBinOfKind(const CoverPoint* cp, CoverBinKind kind,
                               const Matches& matches) {
  return std::ranges::any_of(cp->bins, [&](const CoverBin& bin) {
    return bin.kind == kind && matches(bin);
  });
}

static bool ValueBinTakesHit(const CoverBin& bin, bool value_is_illegal,
                             bool value_is_ignored) {
  if (bin.kind == CoverBinKind::kIllegal || bin.kind == CoverBinKind::kIgnore)
    return false;
  if (value_is_illegal || value_is_ignored) return false;
  return !bin.has_iff_guard || bin.iff_guard_value;
}

template <typename Matches>
static void ScoreSampledValue(CoverPoint* cp, const Matches& matches) {
  bool value_is_illegal =
      ValueHitsBinOfKind(cp, CoverBinKind::kIllegal, matches);
  bool value_is_ignored =
      ValueHitsBinOfKind(cp, CoverBinKind::kIgnore, matches);
  bool matched_defined = false;
  for (size_t i = 0; i < cp->bins.size(); ++i) {
    CoverBin& bin = cp->bins[i];
    if (bin.kind == CoverBinKind::kDefault || !matches(bin)) continue;
    matched_defined = true;
    if (ValueBinTakesHit(bin, value_is_illegal, value_is_ignored)) {
      ++bin.hit_count;
      cp->sampled_bins.push_back(i);
    }
  }
  if (value_is_illegal) ++cp->illegal_violations;
  if (matched_defined) return;
  for (auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kDefault &&
        (!bin.has_iff_guard || bin.iff_guard_value)) {
      ++bin.hit_count;
    }
  }
}

static bool IsTransitionBin(const CoverBin& bin) {
  return bin.kind == CoverBinKind::kTransition ||
         (bin.kind == CoverBinKind::kIllegal && !bin.transitions.empty());
}

static bool CollectTransitionBins(const CoverPoint* cp, size_t& max_seq) {
  max_seq = 0;
  bool any_transition = false;
  for (const auto& bin : cp->bins) {
    if (!IsTransitionBin(bin) || bin.transitions.empty()) continue;
    any_transition = true;
    for (const auto& seq : bin.transitions) {
      if (seq.size() > max_seq) max_seq = seq.size();
    }
  }
  return any_transition;
}

static void AppendSampleHistory(CoverPoint* cp, int64_t value, size_t max_seq) {
  cp->sample_history.push_back(value);
  if (max_seq > 0 && cp->sample_history.size() > max_seq) {
    size_t excess = cp->sample_history.size() - max_seq;
    cp->sample_history.erase(
        cp->sample_history.begin(),
        cp->sample_history.begin() + static_cast<std::ptrdiff_t>(excess));
  }
}

static bool SampleHistoryEndsWith(const CoverPoint* cp,
                                  const std::vector<int64_t>& seq,
                                  size_t length) {
  if (cp->sample_history.size() < length) return false;
  size_t off = cp->sample_history.size() - length;
  for (size_t i = 0; i < length; ++i) {
    if (cp->sample_history[off + i] != seq[i]) return false;
  }
  return true;
}

static bool SampleHistoryMatchesSeq(const CoverPoint* cp,
                                    const std::vector<int64_t>& seq) {
  return !seq.empty() && SampleHistoryEndsWith(cp, seq, seq.size());
}

struct TransitionOutcome {
  bool completed = false;
  bool pending = false;
};

static bool SequenceRemainsPending(const CoverPoint* cp) {
  for (const auto& bin : cp->bins) {
    if (!IsTransitionBin(bin)) continue;
    for (const auto& seq : bin.transitions) {
      for (size_t k = 2; k < seq.size(); ++k) {
        if (SampleHistoryEndsWith(cp, seq, k)) return true;
      }
    }
  }
  return false;
}

static void CountCompletedTransition(CoverPoint* cp, size_t index) {
  CoverBin& bin = cp->bins[index];
  if (bin.kind == CoverBinKind::kIllegal) {
    ++cp->illegal_violations;
    return;
  }
  if (bin.has_iff_guard && !bin.iff_guard_value) return;
  ++bin.hit_count;
  cp->sampled_bins.push_back(index);
}

static void ScoreTransitionBins(CoverPoint* cp, TransitionOutcome& outcome) {
  for (size_t i = 0; i < cp->bins.size(); ++i) {
    CoverBin& bin = cp->bins[i];
    if (!IsTransitionBin(bin)) continue;
    for (const auto& seq : bin.transitions) {
      if (!SampleHistoryMatchesSeq(cp, seq)) continue;
      CountCompletedTransition(cp, i);
      outcome.completed = true;
      break;
    }
  }
}

static bool CollectPatternBins(const CoverPoint* cp) {
  for (const auto& bin : cp->bins) {
    if (!bin.transition_patterns.empty()) return true;
  }
  return false;
}

struct TransitionStepOut {
  std::vector<TransitionMatchThread> next;
  bool completed = false;

  void Emit(TransitionMatchThread t) {
    for (const auto& e : next) {
      if (e.elem == t.elem && e.reps == t.reps && e.gap_ok == t.gap_ok) return;
    }
    next.push_back(t);
  }
};

static bool StepGapThread(const std::vector<TransitionPatternElement>& pat,
                          const TransitionMatchThread& th, int64_t v,
                          bool in_set, TransitionStepOut& out) {
  if (th.elem > 0 && IsInValueSet(pat[th.elem - 1].values, v)) return true;
  if (!in_set) {
    out.Emit(th);
    return true;
  }
  return false;
}

static void StepPlainElement(size_t pat_size, const TransitionMatchThread& th,
                             bool in_set, TransitionStepOut& out) {
  if (!in_set) return;
  if (th.elem + 1 == pat_size) {
    out.completed = true;
    return;
  }
  out.Emit(TransitionMatchThread{th.elem + 1, 0, false});
}

static void StepRepeatElement(const TransitionPatternElement& e,
                              size_t pat_size, const TransitionMatchThread& th,
                              bool in_set, TransitionStepOut& out) {
  if (!in_set) {
    if (th.reps < e.repeat_hi) out.Emit(th);
    return;
  }
  uint32_t r = th.reps + 1;
  if (r > e.repeat_hi) return;
  out.Emit(TransitionMatchThread{th.elem, r, false});
  if (r < e.repeat_lo) return;
  if (th.elem + 1 == pat_size) {
    out.completed = true;
    return;
  }
  bool gap = e.repeat_kind == TransitionRepeatKind::kNonconsecutive;
  out.Emit(TransitionMatchThread{th.elem + 1, 0, gap});
}

static void StepThread(const std::vector<TransitionPatternElement>& pat,
                       const TransitionMatchThread& th, int64_t v,
                       TransitionStepOut& out) {
  const TransitionPatternElement& e = pat[th.elem];
  bool in_set = IsInValueSet(e.values, v);
  if (th.gap_ok && StepGapThread(pat, th, v, in_set, out)) return;
  if (!e.has_repeat) {
    StepPlainElement(pat.size(), th, in_set, out);
    return;
  }
  StepRepeatElement(e, pat.size(), th, in_set, out);
}

static bool AdvanceTransitionPattern(
    const std::vector<TransitionPatternElement>& pat,
    std::vector<TransitionMatchThread>& threads, int64_t v, bool& pending) {
  TransitionStepOut out;
  for (const auto& th : threads) {
    if (th.elem != 0 || th.reps != 0) StepThread(pat, th, v, out);
  }
  if (!out.next.empty()) pending = true;
  StepThread(pat, TransitionMatchThread{0, 0, false}, v, out);
  threads = std::move(out.next);
  return out.completed;
}

static void ScorePatternBins(CoverPoint* cp, int64_t value,
                             TransitionOutcome& outcome) {
  for (size_t b = 0; b < cp->bins.size(); ++b) {
    CoverBin& bin = cp->bins[b];
    if (bin.transition_patterns.empty()) continue;
    if (bin.pattern_threads.size() != bin.transition_patterns.size()) {
      bin.pattern_threads.assign(bin.transition_patterns.size(), {});
    }
    bool completed = false;
    for (size_t i = 0; i < bin.transition_patterns.size(); ++i) {
      if (AdvanceTransitionPattern(bin.transition_patterns[i],
                                   bin.pattern_threads[i], value,
                                   outcome.pending)) {
        completed = true;
      }
    }
    if (completed) {
      CountCompletedTransition(cp, b);
      outcome.completed = true;
    }
  }
}

static void ScoreDefaultSequenceBins(CoverPoint* cp,
                                     const TransitionOutcome& outcome) {
  if (!cp->sampled || !CoverageDB::DefaultSequenceTransitionIncrements(
                          outcome.completed, outcome.pending)) {
    return;
  }
  for (CoverBin& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kDefaultSequence &&
        (!bin.has_iff_guard || bin.iff_guard_value)) {
      ++bin.hit_count;
    }
  }
}

void CoverageDB::SampleCoverPoint(CoverPoint* cp, int64_t value) {
  cp->sampled_bins.clear();
  if (!cp->collecting || (cp->has_iff_guard && !cp->iff_guard_value)) return;
  ScoreSampledValue(cp, [&](const CoverBin& bin) {
    return AutoBinSampleIncluded(cp->sample_has_xz) && MatchesBin(bin, value);
  });

  size_t max_seq = 0;
  TransitionOutcome outcome;
  if (CollectTransitionBins(cp, max_seq)) {
    AppendSampleHistory(cp, value, max_seq);
    ScoreTransitionBins(cp, outcome);
    outcome.pending = SequenceRemainsPending(cp);
  }
  if (CollectPatternBins(cp)) ScorePatternBins(cp, value, outcome);
  ScoreDefaultSequenceBins(cp, outcome);
  cp->sampled = true;
}

static bool MatchesRealBin(const CoverBin& bin, double value) {
  return std::ranges::any_of(bin.real_intervals, [&](const RealInterval& r) {
    return r.low <= value &&
           (value < r.high || (r.high_inclusive && value == r.high));
  });
}

void CoverageDB::SampleRealCoverPoint(CoverPoint* cp, double value) {
  cp->sampled_bins.clear();
  if (!cp->collecting || (cp->has_iff_guard && !cp->iff_guard_value)) return;
  ScoreSampledValue(
      cp, [&](const CoverBin& bin) { return MatchesRealBin(bin, value); });
}

void CoverageDB::SampleCross(
    CrossCover* cross,
    const std::vector<std::pair<std::string, int64_t>>& vals) {
  if (!cross->collecting || (cross->has_iff_guard && !cross->iff_guard_value))
    return;
  for (auto& cbin : cross->bins) {
    if (cbin.has_iff_guard && !cbin.iff_guard_value) continue;
    if (MatchesCrossBin(cbin, cross->coverpoint_names, vals)) {
      ++cbin.hit_count;
    }
  }
}

static bool SampledBinTuple(const std::vector<const CoverPoint*>& points,
                            const std::vector<size_t>& tuple) {
  for (size_t i = 0; i < points.size(); ++i) {
    if (points[i] == nullptr ||
        std::ranges::find(points[i]->sampled_bins, tuple[i]) ==
            points[i]->sampled_bins.end()) {
      return false;
    }
  }
  return true;
}

static std::vector<const CoverPoint*> CrossedPoints(const CoverGroup& group,
                                                    const CrossCover& cross) {
  std::vector<const CoverPoint*> points;
  points.reserve(cross.coverpoint_names.size());
  for (const std::string& name : cross.coverpoint_names) {
    auto it = std::ranges::find(group.coverpoints, name, &CoverPoint::name);
    points.push_back(it == group.coverpoints.end() ? nullptr : &*it);
  }
  return points;
}

bool CoverageDB::CrossTupleSampled(const CoverGroup* group,
                                   const CrossCover* cross,
                                   const std::vector<size_t>& tuple) {
  return SampledBinTuple(CrossedPoints(*group, *cross), tuple);
}

static void SampleCrossBinTuples(const CoverGroup& group, CrossCover& cross) {
  if (!cross.collecting || (cross.has_iff_guard && !cross.iff_guard_value))
    return;
  std::vector<const CoverPoint*> points = CrossedPoints(group, cross);
  for (CrossBin& cbin : cross.bins) {
    if (cbin.has_iff_guard && !cbin.iff_guard_value) continue;
    if (std::ranges::any_of(cbin.bin_tuples, [&](const auto& tuple) {
          return SampledBinTuple(points, tuple);
        })) {
      ++cbin.hit_count;
    }
  }
}

void CoverageDB::Sample(
    CoverGroup* group,
    const std::vector<std::pair<std::string, int64_t>>& values) {
  Sample(group, values, {});
}

void CoverageDB::Sample(
    CoverGroup* group,
    const std::vector<std::pair<std::string, int64_t>>& values,
    const std::vector<std::pair<std::string, double>>& real_values) {
  if (!group->collecting) return;
  ++group->sample_count;
  for (auto& cp : group->coverpoints) {
    cp.sampled_bins.clear();
    for (const auto& [name, val] : values) {
      if (name == cp.name) {
        SampleCoverPoint(&cp, val);
        break;
      }
    }
    for (const auto& [name, val] : real_values) {
      if (name == cp.name) {
        SampleRealCoverPoint(&cp, val);
        break;
      }
    }
  }
  for (auto& cross : group->crosses) {
    SampleCross(&cross, values);
    SampleCrossBinTuples(*group, cross);
  }
}

bool BinParticipates(const CoverBin& bin) {
  if (bin.kind == CoverBinKind::kIllegal) return false;
  if (bin.kind == CoverBinKind::kIgnore) return false;
  if (bin.kind == CoverBinKind::kDefault) return false;
  if (bin.values.empty() && bin.ranges.empty() && bin.real_intervals.empty() &&
      bin.transitions.empty() && bin.transition_patterns.empty()) {
    return false;
  }
  return true;
}

double CoverageDB::GetPointCoverage(const CoverPoint* cp) {
  if (cp->bins.empty()) return 100.0;
  uint32_t total = 0;
  uint32_t covered = 0;
  for (const auto& bin : cp->bins) {
    if (!BinParticipates(bin)) continue;
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
  if (total == 0) {
    return cp->weight == 0 ? 100.0 : 0.0;
  }
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

double CoverageDB::GetCrossCoverage(const CrossCover* cross) {
  uint32_t total = 0;
  uint32_t covered = 0;
  for (const auto& bin : cross->bins) {
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
  if (total == 0) {
    return cross->option.weight == 0 ? 100.0 : 0.0;
  }
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

double CoverageDB::GetCrossCoverage(const CrossCover* cross,
                                    int32_t& covered_bins,
                                    int32_t& total_bins) {
  covered_bins = 0;
  total_bins = 0;
  if (CrossCoverageDenominatorZero(cross)) return GetCrossCoverage(cross);
  for (const auto& bin : cross->bins) {
    ++total_bins;
    if (bin.hit_count >= bin.at_least) ++covered_bins;
  }
  return GetCrossCoverage(cross);
}

double CoverageDB::GetCoverage(const CoverGroup* group) {
  double numerator = 0.0;
  int64_t denominator = 0;
  for (const auto& cp : group->coverpoints) {
    if (cp.excluded_from_coverage) continue;
    if (PointCoverageDenominatorZero(&cp)) continue;
    numerator += static_cast<double>(cp.weight) * GetPointCoverage(&cp);
    denominator += cp.weight;
  }
  for (const auto& cross : group->crosses) {
    if (cross.excluded_from_coverage) continue;
    if (CrossCoverageDenominatorZero(&cross)) continue;
    numerator +=
        static_cast<double>(cross.option.weight) * GetCrossCoverage(&cross);
    denominator += cross.option.weight;
  }
  if (denominator == 0) {
    return group->options.weight == 0 ? 100.0 : 0.0;
  }
  return numerator / static_cast<double>(denominator);
}

double CoverageDB::GetInstCoverage(const CoverGroup* group) {
  return GetCoverage(group);
}

void CoverageDB::Start(CoverGroup* group) { group->collecting = true; }

void CoverageDB::Stop(CoverGroup* group) { group->collecting = false; }

void CoverageDB::SetInstName(CoverGroup* group, std::string name) {
  group->options.name = std::move(name);
}

static void CountPointBins(const CoverPoint* cp, int32_t& covered,
                           int32_t& total) {
  for (const auto& bin : cp->bins) {
    if (!BinParticipates(bin)) continue;
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
}

static void CountCrossBins(const CrossCover* cross, int32_t& covered,
                           int32_t& total) {
  for (const auto& bin : cross->bins) {
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
}

double CoverageDB::GetCoverage(const CoverGroup* group, int32_t& covered_bins,
                               int32_t& total_bins) {
  covered_bins = 0;
  total_bins = 0;
  if (CovergroupCoverageDenominatorZero(group)) return GetCoverage(group);
  for (const auto& cp : group->coverpoints) {
    CountPointBins(&cp, covered_bins, total_bins);
  }
  for (const auto& cross : group->crosses) {
    CountCrossBins(&cross, covered_bins, total_bins);
  }
  return GetCoverage(group);
}

double CoverageDB::GetInstCoverage(const CoverGroup* group,
                                   int32_t& covered_bins, int32_t& total_bins) {
  return GetCoverage(group, covered_bins, total_bins);
}

bool CoverageDB::PointCoverageDenominatorZero(const CoverPoint* cp) {
  for (const auto& bin : cp->bins) {
    if (BinParticipates(bin)) return false;
  }
  return true;
}

double CoverageDB::GetPointCoverage(const CoverPoint* cp, int32_t& covered_bins,
                                    int32_t& total_bins) {
  covered_bins = 0;
  total_bins = 0;
  if (PointCoverageDenominatorZero(cp)) return GetPointCoverage(cp);
  CountPointBins(cp, covered_bins, total_bins);
  return GetPointCoverage(cp);
}

uint32_t CoverageDB::CumulativeAtLeast(
    const std::vector<uint32_t>& at_least_values) {
  uint32_t result = 1;
  for (uint32_t v : at_least_values) {
    result = std::max(result, v);
  }
  return result;
}

uint64_t CoverageDB::CrossAutoBinCount(
    const std::vector<uint64_t>& per_point_bin_counts,
    uint64_t user_defined_cross_products) {
  uint64_t total_products = 1;
  for (uint64_t b_j : per_point_bin_counts) {
    total_products *= b_j;
  }
  if (user_defined_cross_products > total_products) return 0;
  return total_products - user_defined_cross_products;
}

uint64_t CoverageDB::CrossCoverageDenominator(
    const std::vector<uint64_t>& per_point_bin_counts,
    uint64_t user_defined_cross_products, uint64_t significant_user_bins) {
  return CrossAutoBinCount(per_point_bin_counts, user_defined_cross_products) +
         significant_user_bins;
}

bool CoverageDB::CrossBinCountsTowardCoverage(CrossSampleOutcome outcome) {
  return outcome == CrossSampleOutcome::kCounted;
}

bool CoverageDB::CrossCoverageDenominatorZero(const CrossCover* cross) {
  return cross->bins.empty();
}

}  // namespace delta
