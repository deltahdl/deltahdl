#include "simulator/coverage.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
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

void CoverageDB::AutoCreateBins(CoverPoint* cp, int64_t min_val,
                                int64_t max_val) {
  cp->auto_bin_min = min_val;
  cp->auto_bin_max = max_val;
  int64_t range = max_val - min_val + 1;
  uint32_t bin_count = cp->auto_bin_count;
  if (static_cast<int64_t>(bin_count) > range) {
    bin_count = static_cast<uint32_t>(range);
  }
  if (bin_count == 0) return;

  int64_t per_bin = range / static_cast<int64_t>(bin_count);
  int64_t remainder = range % static_cast<int64_t>(bin_count);
  int64_t cursor = min_val;

  for (uint32_t i = 0; i < bin_count; ++i) {
    CoverBin bin;
    bin.name = "auto[" + std::to_string(i) + "]";
    bin.kind = CoverBinKind::kAuto;
    int64_t count = per_bin + (static_cast<int64_t>(i) < remainder ? 1 : 0);
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
    ++bin.hit_count;
  }
  if (!matched_defined) {
    for (auto& bin : cp->bins) {
      if (bin.kind == CoverBinKind::kDefault) ++bin.hit_count;
    }
  }

  // Transition bins count whenever the most recent samples complete one of
  // their value-transition sequences (LRM 19.5).
  size_t max_seq = 0;
  bool any_transition = false;
  for (const auto& bin : cp->bins) {
    if (bin.kind != CoverBinKind::kTransition) continue;
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
    if (bin.kind != CoverBinKind::kTransition) continue;
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
        ++bin.hit_count;
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

double CoverageDB::GetPointCoverage(const CoverPoint* cp) {
  if (cp->bins.empty()) return 100.0;
  uint32_t total = 0;
  uint32_t covered = 0;
  for (const auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIllegal) continue;
    if (bin.kind == CoverBinKind::kIgnore) continue;
    // Coverage shall not account for values captured by default bins (LRM
    // 19.5).
    if (bin.kind == CoverBinKind::kDefault) continue;
    ++total;
    if (bin.hit_count >= bin.at_least) ++covered;
  }
  if (total == 0) return 100.0;
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
    if (bin.kind == CoverBinKind::kIllegal) continue;
    if (bin.kind == CoverBinKind::kIgnore) continue;
    if (bin.kind == CoverBinKind::kDefault) continue;
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

static std::vector<std::vector<int64_t>> DistributeValues(
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
