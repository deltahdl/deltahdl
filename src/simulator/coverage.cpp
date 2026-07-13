#include "simulator/coverage.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/coverage_internal.h"

namespace delta {

static bool MatchesBinValues(const CoverBin& bin, int64_t value) {
  for (int64_t v : bin.values) {
    if (v == value) return true;
  }
  return false;
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
  groups_.push_back(CoverGroup{std::move(name), {}, {}, CoverOptions{}, 0});
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
  group->coverpoints.push_back(
      CoverPoint{std::move(name),
                 {},
                 false,
                 true,
                 0,
                 0,
                 static_cast<uint32_t>(group->options.auto_bin_max)});
  return &group->coverpoints.back();
}

CoverBin* CoverageDB::AddBin(CoverPoint* cp, CoverBin bin) {
  cp->bins.push_back(std::move(bin));
  return &cp->bins.back();
}

bool CoverageDB::AutoBinsAllowed(const CoverPoint* cp) {
  // Automatic bins are created for an integral coverpoint only; a real
  // coverpoint never receives them (LRM 19.5.3).
  return !cp->is_real;
}

bool CoverageDB::ShouldAutoCreateBins(const CoverPoint* cp) {
  // A real coverpoint is never a candidate (LRM 19.5.3).
  if (!AutoBinsAllowed(cp)) return false;
  // Any bin other than an ignore or illegal bin is a user-defined bin that
  // supplies the covered value set, so automatic state bins are not created.
  // Ignore and illegal bins only exclude values and are disregarded when
  // deciding whether the coverpoint defines its own bins (LRM 19.5.3).
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
  // N = MIN(2^M, auto_bin_max), where M is the number of bits needed to
  // represent the coverpoint. A coverpoint wide enough that 2^M overflows is
  // capped by auto_bin_max in practice (LRM 19.5.3).
  uint64_t two_pow_m =
      coverpoint_bits >= 64 ? UINT64_MAX : (uint64_t{1} << coverpoint_bits);
  return std::min(two_pow_m, auto_bin_max);
}

uint64_t CoverageDB::AutoBinCountEnum(uint64_t enum_cardinality) {
  // One automatic bin per enumeration member (LRM 19.5.3).
  return enum_cardinality;
}

bool CoverageDB::AutoBinSampleIncluded(bool sample_has_xz) {
  // Automatically created bins consider 2-state values only; a sample whose
  // value contains x or z is excluded (LRM 19.5.3).
  return !sample_has_xz;
}

std::string CoverageDB::AutoBinName(int64_t low, int64_t high) {
  // A single-value bin is named after that value; a bin spanning a range is
  // named "auto[low:high]" (LRM 19.5.3).
  if (low == high) return "auto[" + std::to_string(low) + "]";
  return "auto[" + std::to_string(low) + ":" + std::to_string(high) + "]";
}

std::string CoverageDB::AutoEnumBinName(std::string_view constant_name) {
  // For an enumerated type the bin name embeds the named constant (LRM 19.5.3).
  return "auto[" + std::string(constant_name) + "]";
}

void CoverageDB::AutoCreateBins(CoverPoint* cp, int64_t min_val,
                                int64_t max_val) {
  // Automatic state bins are created only for an integral coverpoint that
  // defines no bins other than ignore or illegal bins; a real coverpoint or one
  // that already carries user bins is left untouched (LRM 19.5.3).
  if (!ShouldAutoCreateBins(cp)) return;
  cp->auto_bin_min = min_val;
  cp->auto_bin_max = max_val;
  int64_t range = max_val - min_val + 1;
  if (range <= 0) return;
  // The number of bins is N = MIN(2^M, auto_bin_max); the [min,max] window the
  // caller supplies carries the 2^M possible values and auto_bin_count carries
  // the auto_bin_max limit (LRM 19.5.3).
  uint32_t bin_count = cp->auto_bin_count;
  if (static_cast<int64_t>(bin_count) > range) {
    bin_count = static_cast<uint32_t>(range);
  }
  if (bin_count == 0) return;

  // Distribute the 2^M values uniformly across the N bins. When the count does
  // not divide evenly, the last bin absorbs the remaining items, e.g. M=3, N=3
  // yields {0,1}, {2,3}, {4,5,6,7} (LRM 19.5.3).
  int64_t per_bin = range / static_cast<int64_t>(bin_count);
  int64_t cursor = min_val;
  for (uint32_t i = 0; i < bin_count; ++i) {
    bool last = (i + 1 == bin_count);
    int64_t count = last ? (max_val - cursor + 1) : per_bin;
    int64_t low = cursor;
    int64_t high = cursor + count - 1;
    CoverBin bin;
    bin.kind = CoverBinKind::kAuto;
    bin.name = AutoBinName(low, high);
    for (int64_t j = 0; j < count; ++j) {
      bin.values.push_back(cursor + j);
    }
    cursor += count;
    cp->bins.push_back(std::move(bin));
  }
}

CrossCover* CoverageDB::AddCross(CoverGroup* group, CrossCover cross) {
  group->crosses.push_back(std::move(cross));
  return &group->crosses.back();
}

// An illegal bin takes precedence over every other bin: a sampled value that
// hits an illegal state bin is a run-time error and is counted toward no
// coverage bin, even when it also belongs to another bin (LRM 19.5.6).
static bool ValueHitsIllegalBin(const CoverPoint* cp, int64_t value) {
  for (const auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIllegal && MatchesBin(bin, value)) {
      return true;
    }
  }
  return false;
}

// An ignored value is removed from the value set of every coverage bin, so a
// sampled value that hits an ignored state bin counts toward no coverage bin —
// even one it would otherwise share — and is silently excluded from coverage
// with no run-time error (LRM 19.5.5).
static bool ValueHitsIgnoreBin(const CoverPoint* cp, int64_t value) {
  for (const auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIgnore && MatchesBin(bin, value)) {
      return true;
    }
  }
  return false;
}

// Increments every value bin the sample lands in, honoring illegal/ignore
// dominance and per-bin iff guards, and reports whether the value lies within
// any defined (non-default) bin (LRM 19.5, 19.5.1, 19.5.5, 19.5.6).
static bool ScoreValueBins(CoverPoint* cp, int64_t value, bool value_is_illegal,
                           bool value_is_ignored) {
  // A value "lies within a defined bin" if it matches any non-default bin,
  // including illegal and ignore bins. The default bin catches only what the
  // defined bins miss (LRM 19.5).
  bool matched_defined = false;
  for (auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kDefault) continue;
    if (!MatchesBin(bin, value)) continue;
    matched_defined = true;
    if (bin.kind == CoverBinKind::kIllegal) continue;
    if (bin.kind == CoverBinKind::kIgnore) continue;
    // The illegal match dominates this sample, so the value counts toward no
    // other bin (LRM 19.5.6).
    if (value_is_illegal) continue;
    // An ignored value is removed from every coverage bin's value set, so it
    // likewise counts toward no other bin it happens to share (LRM 19.5.5).
    if (value_is_ignored) continue;
    // A per-bin iff guard that is false at this sampling point suppresses the
    // increment for this bin (LRM 19.5.1).
    if (bin.has_iff_guard && !bin.iff_guard_value) continue;
    ++bin.hit_count;
  }
  return matched_defined;
}

// Transition bins count whenever the most recent samples complete one of their
// value-transition sequences (LRM 19.5). An illegal_bins transition bin (kind
// kIllegal carrying transition sequences) is tracked alongside ordinary
// transition bins so that a completed illegal sequence can raise its run-time
// error (LRM 19.5.6).
static bool IsTransitionBin(const CoverBin& bin) {
  return bin.kind == CoverBinKind::kTransition ||
         (bin.kind == CoverBinKind::kIllegal && !bin.transitions.empty());
}

// Reports whether the coverpoint has any bin carrying a concrete transition
// sequence, and through max_seq the longest such sequence. A bin that carries
// only structured goto/nonconsecutive patterns is matched incrementally instead
// and so does not feed the trailing sample window.
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

// Appends the new sample and trims the history to the longest transition
// sequence so older samples that can no longer complete a sequence are dropped.
static void AppendSampleHistory(CoverPoint* cp, int64_t value, size_t max_seq) {
  cp->sample_history.push_back(value);
  if (max_seq > 0 && cp->sample_history.size() > max_seq) {
    size_t excess = cp->sample_history.size() - max_seq;
    cp->sample_history.erase(
        cp->sample_history.begin(),
        cp->sample_history.begin() + static_cast<std::ptrdiff_t>(excess));
  }
}

// Reports whether the most recent samples match this transition sequence.
static bool SampleHistoryMatchesSeq(const CoverPoint* cp,
                                    const std::vector<int64_t>& seq) {
  if (seq.empty() || cp->sample_history.size() < seq.size()) return false;
  size_t off = cp->sample_history.size() - seq.size();
  for (size_t i = 0; i < seq.size(); ++i) {
    if (cp->sample_history[off + i] != seq[i]) return false;
  }
  return true;
}

// Scores any transition bin whose sequence was completed by the latest sample.
static void ScoreTransitionBins(CoverPoint* cp) {
  for (auto& bin : cp->bins) {
    if (!IsTransitionBin(bin)) continue;
    for (const auto& seq : bin.transitions) {
      if (!SampleHistoryMatchesSeq(cp, seq)) continue;
      // A completed illegal transition is a run-time error and counts toward
      // no coverage bin; an ordinary transition bin increments (LRM 19.5.6).
      if (bin.kind == CoverBinKind::kIllegal) {
        ++cp->illegal_violations;
      } else {
        ++bin.hit_count;
      }
      break;
    }
  }
}

// Reports whether the coverpoint has any structured goto/nonconsecutive
// transition pattern bin. Such bins describe sequences of unbounded or varying
// length and are matched incrementally rather than against a trailing window
// (LRM 19.5.2).
static bool CollectPatternBins(const CoverPoint* cp) {
  for (const auto& bin : cp->bins) {
    if (!bin.transition_patterns.empty()) return true;
  }
  return false;
}

// Advances one transition pattern by a single sampled value, updating its live
// thread set and reporting whether the pattern completes on this sample (LRM
// 19.5.2). A fresh match may begin at any sample, so a thread positioned at the
// first element is seeded every time. Each thread records how far it has
// matched and, for a goto or nonconsecutive repetition, how many occurrences it
// has accumulated; a goto requires the following element to immediately follow
// the last occurrence, while a nonconsecutive form tolerates later samples
// before it so long as the repetition value does not recur.
static bool AdvanceTransitionPattern(
    const std::vector<TransitionPatternElement>& pat,
    std::vector<TransitionMatchThread>& threads, int64_t v) {
  std::vector<TransitionMatchThread> next;
  bool completed = false;
  auto emit = [&next](TransitionMatchThread t) {
    for (const auto& e : next) {
      if (e.elem == t.elem && e.reps == t.reps && e.gap_ok == t.gap_ok) return;
    }
    next.push_back(t);
  };

  std::vector<TransitionMatchThread> current = threads;
  current.push_back(TransitionMatchThread{0, 0, false});

  for (const auto& th : current) {
    const TransitionPatternElement& e = pat[th.elem];
    bool in_set = IsInValueSet(e.values, v);

    // After a nonconsecutive repetition, intervening samples are tolerated
    // before the following element as long as the repetition value does not
    // recur; a recurrence voids this branch (the accumulating thread handles
    // the extra occurrence separately).
    if (th.gap_ok) {
      if (th.elem > 0 && IsInValueSet(pat[th.elem - 1].values, v)) continue;
      if (!in_set) {
        emit(th);
        continue;
      }
      // The gap is over: fall through and match this element now.
    }

    if (!e.has_repeat) {
      // A plain element must match the immediately expected sample.
      if (in_set) {
        if (th.elem + 1 == pat.size()) {
          completed = true;
        } else {
          emit(TransitionMatchThread{th.elem + 1, 0, false});
        }
      }
      continue;
    }

    if (in_set) {
      uint32_t r = th.reps + 1;
      if (r > e.repeat_hi) continue;  // too many occurrences: this branch dies
      // Keep accumulating so further occurrences and their gaps can still
      // match.
      emit(TransitionMatchThread{th.elem, r, false});
      if (r >= e.repeat_lo) {
        if (th.elem + 1 == pat.size()) {
          completed = true;
        } else {
          bool gap = e.repeat_kind == TransitionRepeatKind::kNonconsecutive;
          emit(TransitionMatchThread{th.elem + 1, 0, gap});
        }
      }
    } else if (th.reps < e.repeat_hi) {
      // An intervening sample before or between occurrences is allowed while
      // the element can still accept more of them.
      emit(th);
    }
  }

  threads = std::move(next);
  return completed;
}

// Advances every structured transition pattern bin of the coverpoint by the
// latest sampled value, incrementing a bin at most once per sample when any of
// its patterns completes; a completed illegal pattern raises a run-time error
// and counts toward no bin (LRM 19.5.2, 19.5.6).
static void ScorePatternBins(CoverPoint* cp, int64_t value) {
  for (auto& bin : cp->bins) {
    if (bin.transition_patterns.empty()) continue;
    if (bin.pattern_threads.size() != bin.transition_patterns.size()) {
      bin.pattern_threads.assign(bin.transition_patterns.size(), {});
    }
    bool completed = false;
    // Advance every pattern (not just up to the first completion) so all thread
    // state stays consistent for later samples.
    for (size_t i = 0; i < bin.transition_patterns.size(); ++i) {
      if (AdvanceTransitionPattern(bin.transition_patterns[i],
                                   bin.pattern_threads[i], value)) {
        completed = true;
      }
    }
    if (!completed) continue;
    if (bin.kind == CoverBinKind::kIllegal) {
      ++cp->illegal_violations;
    } else {
      ++bin.hit_count;
    }
  }
}

void CoverageDB::SampleCoverPoint(CoverPoint* cp, int64_t value) {
  if (cp->has_iff_guard && !cp->iff_guard_value) return;
  bool value_is_illegal = ValueHitsIllegalBin(cp, value);
  bool value_is_ignored = ValueHitsIgnoreBin(cp, value);
  bool matched_defined =
      ScoreValueBins(cp, value, value_is_illegal, value_is_ignored);
  // Issue the run-time error for an illegal value occurrence (LRM 19.5.6).
  if (value_is_illegal) ++cp->illegal_violations;
  if (!matched_defined) {
    for (auto& bin : cp->bins) {
      if (bin.kind == CoverBinKind::kDefault) ++bin.hit_count;
    }
  }

  // Concrete (bounded) transition sequences match against the trailing sample
  // window; goto/nonconsecutive pattern bins are matched incrementally. Either,
  // both, or neither may be present.
  size_t max_seq = 0;
  if (CollectTransitionBins(cp, max_seq)) {
    AppendSampleHistory(cp, value, max_seq);
    ScoreTransitionBins(cp);
  }
  if (CollectPatternBins(cp)) ScorePatternBins(cp, value);
}

void CoverageDB::SampleCross(
    CrossCover* cross,
    const std::vector<std::pair<std::string, int64_t>>& vals) {
  // A false cross-level iff guard ignores the cross entirely (LRM 19.6).
  if (cross->has_iff_guard && !cross->iff_guard_value) return;
  for (auto& cbin : cross->bins) {
    // A false per-bin iff guard ignores that cross bin (LRM 19.6).
    if (cbin.has_iff_guard && !cbin.iff_guard_value) continue;
    if (MatchesCrossBin(cbin, cross->coverpoint_names, vals)) {
      ++cbin.hit_count;
    }
  }
}

void CoverageDB::Sample(
    CoverGroup* group,
    const std::vector<std::pair<std::string, int64_t>>& values) {
  // A stopped instance ignores triggered samples entirely (LRM 19.8).
  if (!group->collecting) return;
  ++group->sample_count;
  for (auto& cp : group->coverpoints) {
    for (const auto& [name, val] : values) {
      if (name == cp.name) {
        SampleCoverPoint(&cp, val);
        break;
      }
    }
  }
  for (auto& cross : group->crosses) {
    SampleCross(&cross, values);
  }
}

bool BinParticipates(const CoverBin& bin) {
  if (bin.kind == CoverBinKind::kIllegal) return false;
  if (bin.kind == CoverBinKind::kIgnore) return false;
  if (bin.kind == CoverBinKind::kDefault) return false;
  // A bin with no associated value, concrete transition, or structured
  // transition pattern has nothing to cover and does not participate.
  if (bin.values.empty() && bin.transitions.empty() &&
      bin.transition_patterns.empty()) {
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
    // None of the bins has an associated value or transition, so the
    // denominator is zero. A nonzero coverpoint weight reports 0.0; a zero
    // weight reports 100.0 (LRM 19.11.1).
    return cp->weight == 0 ? 100.0 : 0.0;
  }
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

double CoverageDB::GetCrossCoverage(const CrossCover* cross) {
  // The denominator of the cross coverage equation is B_c + B_u (LRM 19.11.2).
  // In this model every stored cross bin is a coverage bin — an auto-cross bin
  // (B_c) or a significant user-defined cross bin (B_u) — so the bin count is
  // exactly that denominator; ignore_bins and illegal_bins products are never
  // stored as bins (LRM 19.6.2, 19.6.3).
  uint32_t total = 0;
  uint32_t covered = 0;
  for (const auto& bin : cross->bins) {
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
  if (total == 0) {
    // A zero denominator reports a weight-dependent value: a nonzero cross
    // weight gives 0.0, a zero weight gives 100.0 (LRM 19.11.2 b, c).
    return cross->option.weight == 0 ? 100.0 : 0.0;
  }
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

double CoverageDB::GetCrossCoverage(const CrossCover* cross,
                                    int32_t& covered_bins,
                                    int32_t& total_bins) {
  covered_bins = 0;
  total_bins = 0;
  // When the cross coverage denominator is zero, both reported counts are zero
  // (LRM 19.11.2 d). Otherwise they are the covered bins (numerator) and the
  // denominator B_c + B_u, which is the stored cross bin count.
  if (CrossCoverageDenominatorZero(cross)) return GetCrossCoverage(cross);
  for (const auto& bin : cross->bins) {
    ++total_bins;
    if (bin.hit_count >= bin.at_least) ++covered_bins;
  }
  return GetCrossCoverage(cross);
}

double CoverageDB::GetCoverage(const CoverGroup* group) {
  // Covergroup coverage is the weighted average of its items' coverage,
  // Cg = Σ(Wi×Ci) / Σ(Wi), where the items are the coverpoints and crosses.
  // An item excluded by its own coverage rules is dropped from both the
  // numerator and the denominator (LRM 19.11).
  double numerator = 0.0;
  int64_t denominator = 0;
  for (const auto& cp : group->coverpoints) {
    if (cp.excluded_from_coverage) continue;
    // A coverpoint whose own denominator is zero does not contribute to the
    // covergroup average; it is dropped from both the numerator and the
    // denominator (LRM 19.11.1).
    if (PointCoverageDenominatorZero(&cp)) continue;
    numerator += static_cast<double>(cp.weight) * GetPointCoverage(&cp);
    denominator += cp.weight;
  }
  for (const auto& cross : group->crosses) {
    if (cross.excluded_from_coverage) continue;
    // A cross whose own coverage denominator B_c + B_u is zero does not
    // contribute to the covergroup average; it is dropped from both the
    // numerator and the denominator (LRM 19.11.2 a).
    if (CrossCoverageDenominatorZero(&cross)) continue;
    numerator +=
        static_cast<double>(cross.option.weight) * GetCrossCoverage(&cross);
    denominator += cross.option.weight;
  }
  if (denominator == 0) {
    // Zero denominator (no items, all weights zero, or all items excluded). A
    // nonzero covergroup weight reports 0.0; a zero covergroup weight reports
    // 100.0 (LRM 19.11).
    return group->options.weight == 0 ? 100.0 : 0.0;
  }
  return numerator / static_cast<double>(denominator);
}

double CoverageDB::GetInstCoverage(const CoverGroup* group) {
  return GetCoverage(group);
}

// --- LRM 19.8: predefined coverage methods ----------------------------------

void CoverageDB::Start(CoverGroup* group) { group->collecting = true; }

void CoverageDB::Stop(CoverGroup* group) { group->collecting = false; }

void CoverageDB::SetInstName(CoverGroup* group, std::string name) {
  group->options.name = std::move(name);
}

// Counts, for a coverpoint, the bins that participate in coverage (excluding
// illegal, ignore, and default bins) and how many of them are covered.
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
  // When the covergroup's coverage denominator is zero, the numerator and
  // denominator reported through the optional ref-int pair are both zero (LRM
  // 19.11). Otherwise they aggregate the covered/defined bin counts across all
  // coverpoints and crosses (LRM 19.8).
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
  // The denominator is zero unless at least one bin participates in the
  // coverage; a bin with no associated value or transition does not (LRM
  // 19.11.1).
  for (const auto& bin : cp->bins) {
    if (BinParticipates(bin)) return false;
  }
  return true;
}

double CoverageDB::GetPointCoverage(const CoverPoint* cp, int32_t& covered_bins,
                                    int32_t& total_bins) {
  covered_bins = 0;
  total_bins = 0;
  // With a zero denominator the reported numerator and denominator are both
  // zero (LRM 19.11.1). Otherwise they are the covered and participating bin
  // counts.
  if (PointCoverageDenominatorZero(cp)) return GetPointCoverage(cp);
  CountPointBins(cp, covered_bins, total_bins);
  return GetPointCoverage(cp);
}

uint32_t CoverageDB::CumulativeAtLeast(
    const std::vector<uint32_t>& at_least_values) {
  // For cumulative coverage a bin is not considered covered unless its hit
  // count reaches the maximum of the at_least values of all instances; the
  // maximum is the more conservative choice (LRM 19.11.1).
  uint32_t result = 1;
  for (uint32_t v : at_least_values) {
    result = std::max(result, v);
  }
  return result;
}

// --- LRM 19.11.2: cross coverage computation --------------------------------

uint64_t CoverageDB::CrossAutoBinCount(
    const std::vector<uint64_t>& per_point_bin_counts,
    uint64_t user_defined_cross_products) {
  // B_c = (∏_j B_j) − B_b. The product over the crossed coverpoints is the
  // total number of cross products; a coverpoint with no bins makes it zero
  // (LRM 19.11.2).
  uint64_t total_products = 1;
  for (uint64_t b_j : per_point_bin_counts) {
    total_products *= b_j;
  }
  // B_b is the subset of cross products comprised by user-defined cross bins,
  // so it never exceeds the total; guard against an ill-formed argument anyway.
  if (user_defined_cross_products > total_products) return 0;
  return total_products - user_defined_cross_products;
}

uint64_t CoverageDB::CrossCoverageDenominator(
    const std::vector<uint64_t>& per_point_bin_counts,
    uint64_t user_defined_cross_products, uint64_t significant_user_bins) {
  // Denominator = B_c + B_u (LRM 19.11.2).
  return CrossAutoBinCount(per_point_bin_counts, user_defined_cross_products) +
         significant_user_bins;
}

bool CoverageDB::CrossBinCountsTowardCoverage(CrossSampleOutcome outcome) {
  // Only a counting cross product contributes a coverage bin; ignored and
  // illegal products (LRM 19.6.2, 19.6.3) are excluded from B_u (LRM 19.11.2).
  return outcome == CrossSampleOutcome::kCounted;
}

bool CoverageDB::CrossCoverageDenominatorZero(const CrossCover* cross) {
  // Every stored cross bin is a coverage bin contributing to B_c + B_u, so the
  // denominator is zero exactly when the cross has no such bins (LRM 19.11.2).
  return cross->bins.empty();
}

double CoverageDB::GetGlobalCoverage() const {
  // $get_coverage reports the overall coverage of all covergroup types as the
  // weighted average of their per-covergroup coverage. Per LRM 19.11, a
  // covergroup whose own denominator is zero does not contribute to the overall
  // score (it is dropped from both the numerator and the denominator), and a
  // design with no contributing covergroups — none exist, or every covergroup
  // has a weight of zero — reports 100.0. ComputeOverallCoverage applies
  // exactly those rules, so $get_coverage routes through it.
  std::vector<const CoverGroup*> instances;
  instances.reserve(groups_.size());
  for (const auto& g : groups_) instances.push_back(&g);
  return ComputeOverallCoverage(instances);
}

}  // namespace delta
