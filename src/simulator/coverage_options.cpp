#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_internal.h"

namespace delta {

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

namespace {

// One member of a merged-instance bin union (LRM 19.11.3). The cumulative count
// of an overlapping bin is the sum of its hit counts in every instance that
// contains it; the at_least values of those instances are kept so the
// conservative cumulative threshold (LRM 19.11.1) can be applied.
struct MergedBin {
  uint64_t hits = 0;
  std::vector<uint32_t> at_least;
};

// Adds a bin's contribution to the union member named by `key`.
void AccumulateMergedBin(std::map<std::string, MergedBin>& bins,
                         const std::string& key, uint64_t hit_count,
                         uint32_t at_least) {
  MergedBin& m = bins[key];
  m.hits += hit_count;
  m.at_least.push_back(at_least);
}

// Counts the unioned bins (the denominator of the merged coverage) and how many
// of them reach the conservative cumulative threshold (the numerator).
void TallyMergedBins(const std::map<std::string, MergedBin>& bins,
                     uint32_t& total, uint32_t& covered) {
  for (const auto& [name, m] : bins) {
    (void)name;
    ++total;
    if (m.hits >= CoverageDB::CumulativeAtLeast(m.at_least)) ++covered;
  }
}

// Adds one covergroup instance's coverpoint bins to the merged-coverpoint union
// (LRM 19.11.3). Names are only meaningful within their item, so each bin is
// keyed by the name of its coverpoint joined with the bin name.
void AccumulateInstancePointBins(const CoverGroup* g,
                                 std::map<std::string, MergedBin>& point_bins) {
  for (const CoverPoint& cp : g->coverpoints) {
    if (cp.excluded_from_coverage) continue;
    for (const CoverBin& bin : cp.bins) {
      if (!BinParticipates(bin)) continue;
      AccumulateMergedBin(point_bins, cp.name + '\x1f' + bin.name,
                          bin.hit_count, bin.at_least);
    }
  }
}

// Adds one covergroup instance's cross bins to the merged-cross union (LRM
// 19.11.3), keyed by the name of the cross joined with the bin name.
void AccumulateInstanceCrossBins(const CoverGroup* g,
                                 std::map<std::string, MergedBin>& cross_bins) {
  for (const CrossCover& cross : g->crosses) {
    if (cross.excluded_from_coverage) continue;
    // Every stored cross bin is a coverage bin; ignore_bins and illegal_bins
    // products are never stored (LRM 19.6.2, 19.6.3, 19.11.2).
    for (const CrossBin& bin : cross.bins) {
      AccumulateMergedBin(cross_bins, cross.name + '\x1f' + bin.name,
                          bin.hit_count, bin.at_least);
    }
  }
}

// Weighted average of the per-instance coverage. The covergroup type coverage
// depends on the instances only, not its coverpoints or crosses, and each
// instance is weighted by its own option.weight (LRM 19.11.3).
double AverageInstanceTypeCoverage(
    const std::vector<const CoverGroup*>& instances) {
  double sum = 0.0;
  uint32_t total_weight = 0;
  for (const CoverGroup* g : instances) {
    sum += CoverageDB::GetCoverage(g) * g->options.weight;
    total_weight += g->options.weight;
  }
  if (total_weight == 0) return 0.0;
  return sum / static_cast<double>(total_weight);
}

}  // namespace

double CoverageDB::ComputeTypeCoverage(
    const std::vector<const CoverGroup*>& instances, bool merge_instances) {
  if (instances.empty()) return 0.0;

  if (!merge_instances) {
    return AverageInstanceTypeCoverage(instances);
  }

  // Merge: union all bins from all instances (LRM 19.11.3). Bins overlap across
  // instances when they share the same name, and the cumulative count of an
  // overlapping bin is the sum of its counts in every instance containing it.
  // Bins with distinct names are distinct members of the union, so instances
  // whose bin layouts differ (for example a different auto_bin_max producing
  // differently named auto bins) enlarge the union rather than collapse onto
  // one another. Names are only meaningful within their item, so coverpoint
  // bins and cross bins are keyed by the name of their coverpoint or cross.
  std::map<std::string, MergedBin> point_bins;
  std::map<std::string, MergedBin> cross_bins;
  for (const CoverGroup* g : instances) {
    AccumulateInstancePointBins(g, point_bins);
    AccumulateInstanceCrossBins(g, cross_bins);
  }
  uint32_t total = 0;
  uint32_t covered = 0;
  TallyMergedBins(point_bins, total, covered);
  TallyMergedBins(cross_bins, total, covered);
  if (total == 0) return 100.0;
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

// --- LRM 19.11.3: type coverage computation ---------------------------------

double CoverageDB::ComputePointTypeCoverage(
    const std::vector<const CoverPoint*>& instances, bool merge_instances) {
  if (instances.empty()) return 0.0;

  if (!merge_instances) {
    // The type coverage of a coverpoint is the coverage of that coverpoint in
    // each instance, weighted by the coverpoint-scope option.weight of the
    // instance (LRM 19.11.3).
    double sum = 0.0;
    int64_t total_weight = 0;
    for (const CoverPoint* cp : instances) {
      sum += GetPointCoverage(cp) * cp->weight;
      total_weight += cp->weight;
    }
    if (total_weight == 0) return 0.0;
    return sum / static_cast<double>(total_weight);
  }

  // Merge: union this coverpoint's bins across instances by bin name, summing
  // the counts of same-named bins (LRM 19.11.3).
  std::map<std::string, MergedBin> bins;
  for (const CoverPoint* cp : instances) {
    for (const CoverBin& bin : cp->bins) {
      if (!BinParticipates(bin)) continue;
      AccumulateMergedBin(bins, bin.name, bin.hit_count, bin.at_least);
    }
  }
  uint32_t total = 0;
  uint32_t covered = 0;
  TallyMergedBins(bins, total, covered);
  if (total == 0) return 100.0;
  return 100.0 * static_cast<double>(covered) / static_cast<double>(total);
}

double CoverageDB::ComputeCrossTypeCoverage(
    const std::vector<const CrossCover*>& instances, bool merge_instances) {
  if (instances.empty()) return 0.0;

  if (!merge_instances) {
    // The type coverage of a cross is the coverage of that cross in each
    // instance, weighted by the cross-scope option.weight (LRM 19.11.3).
    double sum = 0.0;
    int64_t total_weight = 0;
    for (const CrossCover* cross : instances) {
      sum += GetCrossCoverage(cross) * cross->option.weight;
      total_weight += cross->option.weight;
    }
    if (total_weight == 0) return 0.0;
    return sum / static_cast<double>(total_weight);
  }

  // Merge: union this cross's bins across instances by cross-product bin name
  // (LRM 19.11.3). Every stored cross bin is a coverage bin (LRM 19.11.2).
  std::map<std::string, MergedBin> bins;
  for (const CrossCover* cross : instances) {
    for (const CrossBin& bin : cross->bins) {
      AccumulateMergedBin(bins, bin.name, bin.hit_count, bin.at_least);
    }
  }
  uint32_t total = 0;
  uint32_t covered = 0;
  TallyMergedBins(bins, total, covered);
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

}  // namespace delta
