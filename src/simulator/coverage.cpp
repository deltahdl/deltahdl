#include "simulator/coverage.h"

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

static bool IsInValueSet(const std::vector<int64_t>& set, int64_t val) {
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
  group->coverpoints.push_back(CoverPoint{
      std::move(name), {}, false, true, 0, 0, group->options.auto_bin_max});
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
  // No automatic bins for a real coverpoint (LRM 19.5.3).
  if (!AutoBinsAllowed(cp)) return;
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

void CoverageDB::SampleCoverPoint(CoverPoint* cp, int64_t value) {
  if (cp->has_iff_guard && !cp->iff_guard_value) return;
  // An illegal bin takes precedence over every other bin: a sampled value that
  // hits an illegal state bin is a run-time error and is counted toward no
  // coverage bin, even when it also belongs to another bin (LRM 19.5.6).
  bool value_is_illegal = false;
  for (const auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIllegal && MatchesBin(bin, value)) {
      value_is_illegal = true;
      break;
    }
  }
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
    // A per-bin iff guard that is false at this sampling point suppresses the
    // increment for this bin (LRM 19.5.1).
    if (bin.has_iff_guard && !bin.iff_guard_value) continue;
    ++bin.hit_count;
  }
  // Issue the run-time error for an illegal value occurrence (LRM 19.5.6).
  if (value_is_illegal) ++cp->illegal_violations;
  if (!matched_defined) {
    for (auto& bin : cp->bins) {
      if (bin.kind == CoverBinKind::kDefault) ++bin.hit_count;
    }
  }

  // Transition bins count whenever the most recent samples complete one of
  // their value-transition sequences (LRM 19.5).
  // An illegal_bins transition bin (kind kIllegal carrying transition
  // sequences) is tracked alongside ordinary transition bins so that a
  // completed illegal sequence can raise its run-time error (LRM 19.5.6).
  auto is_transition_bin = [](const CoverBin& bin) {
    return bin.kind == CoverBinKind::kTransition ||
           (bin.kind == CoverBinKind::kIllegal && !bin.transitions.empty());
  };
  size_t max_seq = 0;
  bool any_transition = false;
  for (const auto& bin : cp->bins) {
    if (!is_transition_bin(bin)) continue;
    any_transition = true;
    for (const auto& seq : bin.transitions) {
      if (seq.size() > max_seq) max_seq = seq.size();
    }
  }
  if (!any_transition) return;

  cp->sample_history.push_back(value);
  if (max_seq > 0 && cp->sample_history.size() > max_seq) {
    size_t excess = cp->sample_history.size() - max_seq;
    cp->sample_history.erase(
        cp->sample_history.begin(),
        cp->sample_history.begin() + static_cast<std::ptrdiff_t>(excess));
  }

  for (auto& bin : cp->bins) {
    if (!is_transition_bin(bin)) continue;
    for (const auto& seq : bin.transitions) {
      if (seq.empty() || cp->sample_history.size() < seq.size()) continue;
      size_t off = cp->sample_history.size() - seq.size();
      bool match = true;
      for (size_t i = 0; i < seq.size(); ++i) {
        if (cp->sample_history[off + i] != seq[i]) {
          match = false;
          break;
        }
      }
      if (match) {
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

// Whether a coverpoint bin contributes to the coverpoint's coverage numerator
// and denominator. Illegal, ignore, and default bins never contribute (LRM
// 19.5/19.5.6), and a bin with no associated value or transition is excluded
// from both the numerator and the denominator (LRM 19.11.1).
static bool BinParticipates(const CoverBin& bin) {
  if (bin.kind == CoverBinKind::kIllegal) return false;
  if (bin.kind == CoverBinKind::kIgnore) return false;
  if (bin.kind == CoverBinKind::kDefault) return false;
  if (bin.values.empty() && bin.transitions.empty()) return false;
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
  if (cross->bins.empty()) return 100.0;
  uint32_t total = 0;
  uint32_t covered = 0;
  for (const auto& bin : cross->bins) {
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
  if (total == 0) return 100.0;
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
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
  // For cumulative coverage a bin is not considered covered unless its hit count
  // reaches the maximum of the at_least values of all instances; the maximum is
  // the more conservative choice (LRM 19.11.1).
  uint32_t result = 1;
  for (uint32_t v : at_least_values) {
    result = std::max(result, v);
  }
  return result;
}

double CoverageDB::GetGlobalCoverage() const {
  if (groups_.empty()) return 0.0;
  double sum = 0.0;
  uint32_t total_weight = 0;
  for (const auto& g : groups_) {
    sum += GetCoverage(&g) * g.options.weight;
    total_weight += g.options.weight;
  }
  if (total_weight == 0) return 0.0;
  return sum / static_cast<double>(total_weight);
}

// --- LRM 19.9: predefined coverage system tasks and system functions --------

void CoverageDB::SetCoverageDbName(std::string filename) {
  coverage_db_name_ = std::move(filename);
}

const std::string& CoverageDB::CoverageDbName() const {
  return coverage_db_name_;
}

// Accumulates one loaded coverpoint onto a live coverpoint of the same name:
// matching bins add their hit counts, and a bin found only in the loaded data
// is appended (LRM 19.9).
static void MergeLoadedCoverPoint(CoverPoint* live, const CoverPoint& loaded) {
  for (const auto& lb : loaded.bins) {
    CoverBin* match = nullptr;
    for (auto& b : live->bins) {
      if (b.name == lb.name) {
        match = &b;
        break;
      }
    }
    if (match != nullptr) {
      match->hit_count += lb.hit_count;
    } else {
      live->bins.push_back(lb);
    }
  }
}

// Accumulates one loaded cross onto a live cross of the same name, mirroring the
// per-bin accumulation used for coverpoints (LRM 19.9).
static void MergeLoadedCross(CrossCover* live, const CrossCover& loaded) {
  for (const auto& lb : loaded.bins) {
    CrossBin* match = nullptr;
    for (auto& b : live->bins) {
      if (b.name == lb.name) {
        match = &b;
        break;
      }
    }
    if (match != nullptr) {
      match->hit_count += lb.hit_count;
    } else {
      live->bins.push_back(lb);
    }
  }
}

void CoverageDB::MergeCumulativeCoverage(
    const std::vector<CoverGroup>& cumulative) {
  for (const auto& loaded : cumulative) {
    CoverGroup* live = FindGroup(loaded.name);
    if (live == nullptr) {
      // A covergroup type seen only in the persisted database is added in full.
      live = CreateGroup(loaded.name);
      live->coverpoints = loaded.coverpoints;
      live->crosses = loaded.crosses;
      live->options = loaded.options;
      live->type_option = loaded.type_option;
      live->collecting = loaded.collecting;
      live->sample_count = loaded.sample_count;
      continue;
    }

    // The loaded coverage is cumulative, so its counts add to the live ones.
    live->sample_count += loaded.sample_count;
    for (const auto& lcp : loaded.coverpoints) {
      CoverPoint* match = nullptr;
      for (auto& cp : live->coverpoints) {
        if (cp.name == lcp.name) {
          match = &cp;
          break;
        }
      }
      if (match != nullptr) {
        MergeLoadedCoverPoint(match, lcp);
      } else {
        live->coverpoints.push_back(lcp);
      }
    }
    for (const auto& lcross : loaded.crosses) {
      CrossCover* match = nullptr;
      for (auto& cross : live->crosses) {
        if (cross.name == lcross.name) {
          match = &cross;
          break;
        }
      }
      if (match != nullptr) {
        MergeLoadedCross(match, lcross);
      } else {
        live->crosses.push_back(lcross);
      }
    }
  }
}

// --- LRM 19.6: cross coverage -----------------------------------------------

void CoverageDB::EnsureCrossCoverPoints(
    CoverGroup* group, const std::vector<std::string>& names) {
  for (const auto& name : names) {
    bool found = false;
    for (const auto& cp : group->coverpoints) {
      if (cp.name == name) {
        found = true;
        break;
      }
    }
    // A bare variable used in a cross is given an implicit coverpoint, just as
    // though "coverpoint <var>;" had been written (LRM 19.6).
    if (!found) AddCoverPoint(group, name);
  }
}

bool CoverageDB::CrossItemsInSameGroup(const CoverGroup* group,
                                       const std::vector<std::string>& names) {
  for (const auto& name : names) {
    bool found = false;
    for (const auto& cp : group->coverpoints) {
      if (cp.name == name) {
        found = true;
        break;
      }
    }
    if (!found) return false;
  }
  return true;
}

void CoverageDB::AutoCreateCrossBins(CoverGroup* group, CrossCover* cross) {
  // Collect, for each crossed coverpoint, the value lists of the bins that may
  // contribute a cross product. Default, ignore, and illegal bins are skipped
  // (LRM 19.6).
  std::vector<std::vector<std::vector<int64_t>>> per_point;
  for (const auto& name : cross->coverpoint_names) {
    CoverPoint* cp = nullptr;
    for (auto& candidate : group->coverpoints) {
      if (candidate.name == name) {
        cp = &candidate;
        break;
      }
    }
    std::vector<std::vector<int64_t>> contributing;
    if (cp != nullptr) {
      for (const auto& bin : cp->bins) {
        if (bin.kind == CoverBinKind::kDefault) continue;
        if (bin.kind == CoverBinKind::kIgnore) continue;
        if (bin.kind == CoverBinKind::kIllegal) continue;
        contributing.push_back(bin.values);
      }
    }
    per_point.push_back(std::move(contributing));
  }

  cross->bins.clear();
  // Any constituent coverpoint with no contributing bin yields an empty
  // Cartesian product.
  for (const auto& point : per_point) {
    if (point.empty()) return;
  }

  // Iterate the Cartesian product of the per-coverpoint bin lists.
  std::vector<size_t> idx(per_point.size(), 0);
  while (true) {
    CrossBin cbin;
    cbin.value_sets.reserve(per_point.size());
    cbin.name = "<";
    for (size_t i = 0; i < per_point.size(); ++i) {
      cbin.value_sets.push_back(per_point[i][idx[i]]);
      if (i != 0) cbin.name += ",";
      cbin.name += std::to_string(idx[i]);
    }
    cbin.name += ">";
    cross->bins.push_back(std::move(cbin));

    size_t pos = per_point.size();
    while (pos > 0) {
      --pos;
      if (++idx[pos] < per_point[pos].size()) break;
      idx[pos] = 0;
      if (pos == 0) return;
    }
  }
}

bool CoverageDB::CrossBareVariableAllowed(bool variable_is_real) {
  return !variable_is_real;
}

// --- LRM 19.6.1: defining cross coverage bins -------------------------------

std::vector<int64_t> CoverageDB::BinsofBinValues(const CoverBin& bin) {
  // A transition bin has no value set of its own; binsof intersects against the
  // last value of each of its transition sequences (LRM 19.6.1.1).
  if (!bin.transitions.empty()) {
    std::vector<int64_t> last_values;
    for (const auto& seq : bin.transitions) {
      if (!seq.empty()) last_values.push_back(seq.back());
    }
    return last_values;
  }
  return bin.values;
}

std::vector<std::vector<int64_t>> CoverageDB::BinsofYield(const CoverPoint* cp,
                                                          int64_t bin_index) {
  std::vector<std::vector<int64_t>> yielded;
  if (cp == nullptr) return yielded;
  if (bin_index >= 0) {
    // binsof(cp.bin) yields the single named coverpoint bin.
    if (static_cast<size_t>(bin_index) < cp->bins.size()) {
      yielded.push_back(BinsofBinValues(cp->bins[static_cast<size_t>(bin_index)]));
    }
    return yielded;
  }
  // binsof(cp) yields every bin of the coverpoint.
  for (const auto& bin : cp->bins) {
    yielded.push_back(BinsofBinValues(bin));
  }
  return yielded;
}

std::vector<size_t> CoverageDB::SelectBinsByIntersect(
    const std::vector<std::vector<int64_t>>& bins,
    const std::vector<int64_t>& values, bool negate) {
  std::vector<size_t> selected;
  for (size_t i = 0; i < bins.size(); ++i) {
    bool intersects = false;
    for (int64_t v : bins[i]) {
      if (IsInValueSet(values, v)) {
        intersects = true;
        break;
      }
    }
    // The inclusion form keeps the bins that intersect the desired values; the
    // negated form keeps those that do not (LRM 19.6.1).
    if (intersects != negate) selected.push_back(i);
  }
  return selected;
}

std::vector<std::vector<size_t>> CoverageDB::EnumerateCrossProducts(
    const std::vector<size_t>& per_point_bin_counts) {
  std::vector<std::vector<size_t>> products;
  if (per_point_bin_counts.empty()) return products;
  for (size_t count : per_point_bin_counts) {
    if (count == 0) return products;
  }
  std::vector<size_t> idx(per_point_bin_counts.size(), 0);
  while (true) {
    products.push_back(idx);
    size_t pos = per_point_bin_counts.size();
    while (true) {
      --pos;
      if (++idx[pos] < per_point_bin_counts[pos]) break;
      idx[pos] = 0;
      if (pos == 0) return products;
    }
  }
}

std::vector<std::vector<size_t>> CoverageDB::SelectProductsByPointBins(
    const std::vector<size_t>& per_point_bin_counts, size_t point,
    const std::vector<size_t>& selected_point_bins) {
  std::vector<std::vector<size_t>> selected;
  for (const auto& product : EnumerateCrossProducts(per_point_bin_counts)) {
    if (point >= product.size()) continue;
    if (std::find(selected_point_bins.begin(), selected_point_bins.end(),
                  product[point]) != selected_point_bins.end()) {
      selected.push_back(product);
    }
  }
  return selected;
}

std::vector<std::vector<size_t>> CoverageDB::AndCrossSelections(
    const std::vector<std::vector<size_t>>& lhs,
    const std::vector<std::vector<size_t>>& rhs) {
  std::vector<std::vector<size_t>> both;
  for (const auto& p : lhs) {
    if (std::find(rhs.begin(), rhs.end(), p) != rhs.end()) both.push_back(p);
  }
  return both;
}

std::vector<std::vector<size_t>> CoverageDB::OrCrossSelections(
    const std::vector<std::vector<size_t>>& lhs,
    const std::vector<std::vector<size_t>>& rhs) {
  std::vector<std::vector<size_t>> either = lhs;
  for (const auto& q : rhs) {
    if (std::find(either.begin(), either.end(), q) == either.end()) {
      either.push_back(q);
    }
  }
  return either;
}

std::vector<std::vector<size_t>> CoverageDB::RetainedAutoCrossProducts(
    const std::vector<size_t>& per_point_bin_counts,
    const std::vector<std::vector<size_t>>& user_selected_products,
    bool retain_auto_bins) {
  std::vector<std::vector<size_t>> retained;
  if (!retain_auto_bins) return retained;
  for (const auto& product : EnumerateCrossProducts(per_point_bin_counts)) {
    if (std::find(user_selected_products.begin(),
                  user_selected_products.end(),
                  product) == user_selected_products.end()) {
      retained.push_back(product);
    }
  }
  return retained;
}

// --- LRM 19.6.1.2: cross bin with covergroup expressions --------------------

uint64_t CoverageDB::CountSatisfyingValueTuples(
    const std::vector<std::vector<int64_t>>& bin_tuple_value_sets,
    const std::function<bool(const std::vector<int64_t>&)>& pred) {
  // No coverpoints, or any coverpoint with an empty value set, yields no value
  // tuples, hence nothing can satisfy the expression.
  if (bin_tuple_value_sets.empty()) return 0;
  for (const auto& values : bin_tuple_value_sets) {
    if (values.empty()) return 0;
  }
  uint64_t satisfying = 0;
  std::vector<size_t> idx(bin_tuple_value_sets.size(), 0);
  std::vector<int64_t> tuple(bin_tuple_value_sets.size());
  while (true) {
    for (size_t i = 0; i < bin_tuple_value_sets.size(); ++i) {
      tuple[i] = bin_tuple_value_sets[i][idx[i]];
    }
    if (pred(tuple)) ++satisfying;
    size_t pos = bin_tuple_value_sets.size();
    while (true) {
      --pos;
      if (++idx[pos] < bin_tuple_value_sets[pos].size()) break;
      idx[pos] = 0;
      if (pos == 0) return satisfying;
    }
  }
}

std::vector<size_t> CoverageDB::SelectCrossBinTuples(
    const std::vector<std::vector<std::vector<int64_t>>>& candidate_bin_tuples,
    const std::function<bool(const std::vector<int64_t>&)>* pred,
    const CrossWithMatchPolicy& policy) {
  std::vector<size_t> selected;
  for (size_t c = 0; c < candidate_bin_tuples.size(); ++c) {
    // A bare cross_identifier (no with clause) keeps every candidate bin tuple.
    if (pred == nullptr) {
      selected.push_back(c);
      continue;
    }
    const auto& sets = candidate_bin_tuples[c];
    uint64_t satisfying = CountSatisfyingValueTuples(sets, *pred);
    bool keep;
    if (policy.require_all) {
      // The $ form requires every value tuple to satisfy the expression.
      uint64_t total = sets.empty() ? 0 : 1;
      for (const auto& values : sets) total *= values.size();
      keep = total > 0 && satisfying == total;
    } else {
      keep = satisfying >= policy.min_count;
    }
    if (keep) selected.push_back(c);
  }
  return selected;
}

// --- LRM 19.6.2: excluding cross products -----------------------------------

std::vector<std::vector<size_t>> CoverageDB::ExcludeIgnoredCrossProducts(
    const std::vector<std::vector<size_t>>& products,
    const std::vector<std::vector<size_t>>& ignored) {
  // Every cross product that satisfies the ignore_bins select expression is
  // dropped; the rest keep their order (LRM 19.6.2).
  std::vector<std::vector<size_t>> kept;
  for (const auto& product : products) {
    if (std::find(ignored.begin(), ignored.end(), product) == ignored.end()) {
      kept.push_back(product);
    }
  }
  return kept;
}

bool CoverageDB::IgnoredCrossProductRetained(bool /*also_in_other_cross_bin*/) {
  // An ignored cross product is never retained: its exclusion takes precedence
  // over inclusion in any other cross coverage bin of the enclosing cross
  // (LRM 19.6.2).
  return false;
}

// --- LRM 19.6.3: specifying illegal cross products --------------------------

std::vector<std::vector<size_t>> CoverageDB::ExcludeIllegalCrossProducts(
    const std::vector<std::vector<size_t>>& products,
    const std::vector<std::vector<size_t>>& illegal) {
  // Every cross product that satisfies the illegal_bins select expression is
  // excluded from coverage, just as for ignore_bins; the rest keep their order
  // (LRM 19.6.3).
  std::vector<std::vector<size_t>> kept;
  for (const auto& product : products) {
    if (std::find(illegal.begin(), illegal.end(), product) == illegal.end()) {
      kept.push_back(product);
    }
  }
  return kept;
}

CrossSampleOutcome CoverageDB::ClassifyCrossSample(
    const std::vector<size_t>& product,
    const std::vector<std::vector<size_t>>& illegal,
    const std::vector<std::vector<size_t>>& ignored,
    bool /*also_in_other_cross_bin*/) {
  // Illegal takes precedence over every other treatment: if the product is
  // selected by illegal_bins it raises a run-time error and counts toward no
  // coverage, regardless of whether it is also ignored or included in another
  // cross bin (LRM 19.6.3).
  if (std::find(illegal.begin(), illegal.end(), product) != illegal.end()) {
    return CrossSampleOutcome::kIllegalError;
  }
  // A non-illegal product selected by ignore_bins is excluded with no error
  // (LRM 19.6.2).
  if (std::find(ignored.begin(), ignored.end(), product) != ignored.end()) {
    return CrossSampleOutcome::kIgnored;
  }
  return CrossSampleOutcome::kCounted;
}

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

std::vector<RealInterval> CoverageDB::RealRangeIntervals(double low, double high,
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
  int64_t total = static_cast<int64_t>(values.size());
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
  std::vector<int64_t> out;
  for (int64_t v = lo;; ++v) {
    out.push_back(v);
    if (v == hi) break;  // terminate here to stay safe when hi == INT64_MAX
  }
  return out;
}

// --- LRM 19.7: instance coverage options ------------------------------------

bool CoverageDB::OptionWeightValid(int32_t weight) {
  // The weight option shall be a non-negative integral value (LRM 19.7, Table
  // 19-1). Integrality is guaranteed by the parameter type.
  return weight >= 0;
}

bool CoverageDB::OptionSpecifiedMoreThanOnce(
    const std::vector<InstanceOptionKind>& assigned) {
  for (size_t i = 0; i < assigned.size(); ++i) {
    for (size_t j = i + 1; j < assigned.size(); ++j) {
      if (assigned[i] == assigned[j]) return true;
    }
  }
  return false;
}

bool CoverageDB::OptionAllowedAt(InstanceOptionKind kind,
                                 CoverSyntacticLevel level) {
  switch (kind) {
    case InstanceOptionKind::kWeight:
    case InstanceOptionKind::kGoal:
    case InstanceOptionKind::kComment:
    case InstanceOptionKind::kAtLeast:
      // Allowed at covergroup, coverpoint, and cross (LRM 19.7, Table 19-2).
      return true;
    case InstanceOptionKind::kAutoBinMax:
    case InstanceOptionKind::kDetectOverlap:
      // Covergroup and coverpoint, but not cross.
      return level != CoverSyntacticLevel::kCross;
    case InstanceOptionKind::kCrossNumPrintMissing:
    case InstanceOptionKind::kCrossRetainAutoBins:
      // Covergroup and cross, but not coverpoint.
      return level != CoverSyntacticLevel::kCoverpoint;
    case InstanceOptionKind::kName:
    case InstanceOptionKind::kPerInstance:
    case InstanceOptionKind::kGetInstCoverage:
      // Covergroup level only.
      return level == CoverSyntacticLevel::kCovergroup;
  }
  return false;
}

bool CoverageDB::OptionDefaultsToLowerLevels(InstanceOptionKind kind) {
  // Options set at the covergroup level act as defaults for the coverpoints and
  // crosses, except weight, goal, comment, and per_instance (LRM 19.7). name
  // and get_inst_coverage are covergroup-only, so they never propagate either.
  switch (kind) {
    case InstanceOptionKind::kAtLeast:
    case InstanceOptionKind::kAutoBinMax:
    case InstanceOptionKind::kCrossNumPrintMissing:
    case InstanceOptionKind::kCrossRetainAutoBins:
    case InstanceOptionKind::kDetectOverlap:
      return true;
    case InstanceOptionKind::kName:
    case InstanceOptionKind::kWeight:
    case InstanceOptionKind::kGoal:
    case InstanceOptionKind::kComment:
    case InstanceOptionKind::kPerInstance:
    case InstanceOptionKind::kGetInstCoverage:
      return false;
  }
  return false;
}

bool CoverageDB::OptionSettableProcedurally(InstanceOptionKind kind) {
  // per_instance and get_inst_coverage are definition-only; auto_bin_max,
  // detect_overlap, and cross_retain_auto_bins are covergroup/coverpoint
  // definition-only. Everything else may be assigned procedurally after
  // instantiation (LRM 19.7).
  switch (kind) {
    case InstanceOptionKind::kPerInstance:
    case InstanceOptionKind::kGetInstCoverage:
    case InstanceOptionKind::kAutoBinMax:
    case InstanceOptionKind::kDetectOverlap:
    case InstanceOptionKind::kCrossRetainAutoBins:
      return false;
    case InstanceOptionKind::kName:
    case InstanceOptionKind::kWeight:
    case InstanceOptionKind::kGoal:
    case InstanceOptionKind::kComment:
    case InstanceOptionKind::kAtLeast:
    case InstanceOptionKind::kCrossNumPrintMissing:
      return true;
  }
  return false;
}

// --- LRM 19.7.1: covergroup type options ------------------------------------

double CoverageDB::ComputeTypeCoverage(
    const std::vector<const CoverGroup*>& instances, bool merge_instances) {
  if (instances.empty()) return 0.0;

  if (!merge_instances) {
    // Weighted average of the per-instance coverage (LRM 19.7.1).
    double sum = 0.0;
    uint32_t total_weight = 0;
    for (const CoverGroup* g : instances) {
      sum += GetCoverage(g) * g->options.weight;
      total_weight += g->options.weight;
    }
    if (total_weight == 0) return 0.0;
    return sum / static_cast<double>(total_weight);
  }

  // Merge: a bin is covered if it is covered in any instance, i.e. the union
  // of coverage across instances (LRM 19.7.1). All instances share a covergroup
  // type and therefore the same coverpoint/bin layout.
  const CoverGroup* first = instances.front();
  uint32_t total = 0;
  uint32_t covered = 0;
  for (size_t p = 0; p < first->coverpoints.size(); ++p) {
    for (size_t b = 0; b < first->coverpoints[p].bins.size(); ++b) {
      const CoverBin& proto = first->coverpoints[p].bins[b];
      if (proto.kind == CoverBinKind::kIllegal) continue;
      if (proto.kind == CoverBinKind::kIgnore) continue;
      if (proto.kind == CoverBinKind::kDefault) continue;
      ++total;
      uint64_t merged_hits = 0;
      for (const CoverGroup* g : instances) {
        if (p < g->coverpoints.size() && b < g->coverpoints[p].bins.size()) {
          merged_hits += g->coverpoints[p].bins[b].hit_count;
        }
      }
      if (merged_hits >= proto.at_least) ++covered;
    }
  }
  if (total == 0) return 100.0;
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

bool CoverageDB::TypeOptionAllowedAt(TypeOptionKind kind,
                                     CoverSyntacticLevel level) {
  switch (kind) {
    case TypeOptionKind::kWeight:
    case TypeOptionKind::kGoal:
    case TypeOptionKind::kComment:
      // Allowed at covergroup, coverpoint, and cross (LRM 19.7.1, Table 19-4).
      return true;
    case TypeOptionKind::kStrobe:
    case TypeOptionKind::kMergeInstances:
    case TypeOptionKind::kDistributeFirst:
      // Covergroup level only.
      return level == CoverSyntacticLevel::kCovergroup;
    case TypeOptionKind::kRealInterval:
      // Covergroup and coverpoint, but not cross.
      return level != CoverSyntacticLevel::kCross;
  }
  return false;
}

bool CoverageDB::TypeOptionDefaultsToLowerLevels(TypeOptionKind kind) {
  // Only real_interval propagates as a default to lower syntactic levels when
  // set at the covergroup level (LRM 19.7.1).
  return kind == TypeOptionKind::kRealInterval;
}

bool CoverageDB::TypeOptionSettableProcedurally(TypeOptionKind kind) {
  // strobe and real_interval may only be set in the covergroup definition; the
  // other type options may also be assigned procedurally (LRM 19.7.1).
  return kind != TypeOptionKind::kStrobe &&
         kind != TypeOptionKind::kRealInterval;
}

// --- LRM 19.11: coverage computation ----------------------------------------

bool CoverageDB::CovergroupCoverageDenominatorZero(const CoverGroup* group) {
  // The denominator Σ Wi sums the weights of the items that participate in the
  // covergroup average. Excluded items contribute no weight (LRM 19.11).
  int64_t denominator = 0;
  for (const auto& cp : group->coverpoints) {
    if (cp.excluded_from_coverage) continue;
    denominator += cp.weight;
  }
  for (const auto& cross : group->crosses) {
    if (cross.excluded_from_coverage) continue;
    denominator += cross.option.weight;
  }
  return denominator == 0;
}

double CoverageDB::ComputeOverallCoverage(
    const std::vector<const CoverGroup*>& instances) {
  // Weighted average over the covergroup instances. An instance whose own
  // denominator is zero does not contribute to the overall score, so it is
  // left out of both the numerator and the denominator (LRM 19.11).
  double numerator = 0.0;
  int64_t denominator = 0;
  for (const CoverGroup* g : instances) {
    if (CovergroupCoverageDenominatorZero(g)) continue;
    numerator += GetCoverage(g) * static_cast<double>(g->options.weight);
    denominator += g->options.weight;
  }
  // No contributing instance — none exist, or every covergroup weight is
  // zero — yields full coverage (LRM 19.11).
  if (denominator == 0) return 100.0;
  return numerator / static_cast<double>(denominator);
}

void CoverageDB::ApplyDerivedCoverpointOverrides(
    CoverGroup* base,
    const std::vector<std::string>& derived_coverpoint_names) {
  // LRM 19.4.1: a derived coverpoint whose name matches a base coverpoint
  // overrides it; the overridden base coverpoint no longer contributes to the
  // coverage computation.
  for (CoverPoint& cp : base->coverpoints) {
    if (std::find(derived_coverpoint_names.begin(),
                  derived_coverpoint_names.end(),
                  cp.name) != derived_coverpoint_names.end()) {
      cp.excluded_from_coverage = true;
    }
  }
}

void CoverageDB::ApplyDerivedCrossOverrides(
    CoverGroup* base, const std::vector<std::string>& derived_cross_names) {
  // LRM 19.4.1: a base cross stops contributing only when the derived covergroup
  // defines a cross with the same name. A base cross whose coverpoint was
  // overridden still contributes as long as no derived cross shares its name.
  for (CrossCover& cross : base->crosses) {
    if (std::find(derived_cross_names.begin(), derived_cross_names.end(),
                  cross.name) != derived_cross_names.end()) {
      cross.excluded_from_coverage = true;
    }
  }
}

bool CoverageDB::CovergroupTypesAggregate(std::string_view type_a,
                                          std::string_view type_b) {
  // LRM 19.4.1: only instances of the same covergroup type aggregate for type
  // coverage. A derived covergroup names a different type than its base, so the
  // two never aggregate.
  return type_a == type_b;
}

}
