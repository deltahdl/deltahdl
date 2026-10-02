#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_internal.h"
#include "simulator/coverage_types.h"

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

// One coverpoint's or cross's bins unioned over the instances (LRM 19.11.3),
// and the type_option.weight its merged coverage is weighed by (LRM 19.7.1).
struct MergedItem {
  std::map<std::string, MergedBin> bins;
  int32_t weight = 1;
};

// Adds one covergroup instance's coverpoint and cross bins to the union of
// each item's (LRM 19.11.3). Bin names are only meaningful within their item,
// and the names of a covergroup's coverpoints and crosses are distinct, so
// each item is kept under its own name.
void AccumulateInstanceItems(const CoverGroup* g,
                             std::map<std::string, MergedItem>& items) {
  for (const CoverPoint& cp : g->coverpoints) {
    if (cp.excluded_from_coverage) continue;
    MergedItem& item = items[cp.name];
    item.weight = cp.type_weight;
    for (const CoverBin& bin : cp.bins) {
      if (!BinParticipates(bin)) continue;
      AccumulateMergedBin(item.bins, bin.name, bin.hit_count, bin.at_least);
    }
  }
  for (const CrossCover& cross : g->crosses) {
    if (cross.excluded_from_coverage) continue;
    MergedItem& item = items[cross.name];
    item.weight = cross.type_option.weight;
    // Every stored cross bin is a coverage bin; ignore_bins and illegal_bins
    // products are never stored (LRM 19.6.2, 19.6.3, 19.11.2).
    for (const CrossBin& bin : cross.bins) {
      AccumulateMergedBin(item.bins, bin.name, bin.hit_count, bin.at_least);
    }
  }
}

// The average of each item's merged coverage weighed by its type weight (LRM
// 19.7.1). An item with no bin adds nothing, and a covergroup with none is
// fully covered.
double WeighMergedItems(const std::map<std::string, MergedItem>& items) {
  double sum = 0.0;
  int64_t total_weight = 0;
  bool any = false;
  for (const auto& [name, item] : items) {
    (void)name;
    uint32_t total = 0;
    uint32_t covered = 0;
    TallyMergedBins(item.bins, total, covered);
    if (total == 0) continue;
    any = true;
    sum += 100.0 * static_cast<double>(covered) / static_cast<double>(total) *
           item.weight;
    total_weight += item.weight;
  }
  if (!any) return 100.0;
  if (total_weight == 0) return 0.0;
  return sum / static_cast<double>(total_weight);
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

  // Merge: each coverpoint and cross is merged over the instances, the union
  // of its bins there, and the type coverage weighs each item's merged
  // coverage by its type_option.weight (LRM 19.7.1, 19.11.3). Bins overlap
  // across instances when they share the same name, and the cumulative count
  // of an overlapping bin is the sum of its counts in every instance
  // containing it. Bins with distinct names are distinct members of the
  // union, so instances whose bin layouts differ (for example a different
  // auto_bin_max producing differently named auto bins) enlarge the union
  // rather than collapse onto one another.
  std::map<std::string, MergedItem> items;
  for (const CoverGroup* g : instances) AccumulateInstanceItems(g, items);
  return WeighMergedItems(items);
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
