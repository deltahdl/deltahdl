#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_internal.h"
#include "simulator/coverage_types.h"

namespace delta {

bool CoverageDB::OptionWeightValid(int32_t weight) { return weight >= 0; }

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
      return true;
    case InstanceOptionKind::kAutoBinMax:
    case InstanceOptionKind::kDetectOverlap:
      return level != CoverSyntacticLevel::kCross;
    case InstanceOptionKind::kCrossNumPrintMissing:
    case InstanceOptionKind::kCrossRetainAutoBins:
      return level != CoverSyntacticLevel::kCoverpoint;
    case InstanceOptionKind::kName:
    case InstanceOptionKind::kPerInstance:
    case InstanceOptionKind::kGetInstCoverage:
      return level == CoverSyntacticLevel::kCovergroup;
  }
  return false;
}

bool CoverageDB::OptionDefaultsToLowerLevels(InstanceOptionKind kind) {
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

namespace {

struct MergedBin {
  uint64_t hits = 0;
  std::vector<uint32_t> at_least;
};

void AccumulateMergedBin(std::map<std::string, MergedBin>& bins,
                         const std::string& key, uint64_t hit_count,
                         uint32_t at_least) {
  MergedBin& m = bins[key];
  m.hits += hit_count;
  m.at_least.push_back(at_least);
}

void TallyMergedBins(const std::map<std::string, MergedBin>& bins,
                     uint32_t& total, uint32_t& covered) {
  for (const auto& [name, m] : bins) {
    (void)name;
    ++total;
    if (m.hits >= CoverageDB::CumulativeAtLeast(m.at_least)) ++covered;
  }
}

struct MergedItem {
  std::map<std::string, MergedBin> bins;
  int32_t weight = 1;
};

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
    for (const CrossBin& bin : cross.bins) {
      AccumulateMergedBin(item.bins, bin.name, bin.hit_count, bin.at_least);
    }
  }
}

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

  std::map<std::string, MergedItem> items;
  for (const CoverGroup* g : instances) AccumulateInstanceItems(g, items);
  return WeighMergedItems(items);
}

double CoverageDB::ComputePointTypeCoverage(
    const std::vector<const CoverPoint*>& instances, bool merge_instances) {
  if (instances.empty()) return 0.0;

  if (!merge_instances) {
    double sum = 0.0;
    int64_t total_weight = 0;
    for (const CoverPoint* cp : instances) {
      sum += GetPointCoverage(cp) * cp->weight;
      total_weight += cp->weight;
    }
    if (total_weight == 0) return 0.0;
    return sum / static_cast<double>(total_weight);
  }

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
    double sum = 0.0;
    int64_t total_weight = 0;
    for (const CrossCover* cross : instances) {
      sum += GetCrossCoverage(cross) * cross->option.weight;
      total_weight += cross->option.weight;
    }
    if (total_weight == 0) return 0.0;
    return sum / static_cast<double>(total_weight);
  }

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
      return true;
    case TypeOptionKind::kStrobe:
    case TypeOptionKind::kMergeInstances:
    case TypeOptionKind::kDistributeFirst:
      return level == CoverSyntacticLevel::kCovergroup;
    case TypeOptionKind::kRealInterval:
      return level != CoverSyntacticLevel::kCross;
  }
  return false;
}

bool CoverageDB::TypeOptionDefaultsToLowerLevels(TypeOptionKind kind) {
  return kind == TypeOptionKind::kRealInterval;
}

bool CoverageDB::TypeOptionSettableProcedurally(TypeOptionKind kind) {
  return kind != TypeOptionKind::kStrobe &&
         kind != TypeOptionKind::kRealInterval;
}

}  // namespace delta
