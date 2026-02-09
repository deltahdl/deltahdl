#include "simulation/coverage.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

// =============================================================================
// Bin matching helpers (must precede methods that call them)
// =============================================================================

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

// Find the sample value for a named coverpoint, or return false if absent.
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

// Check if a value appears in a set of integers.
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

// =============================================================================
// CoverageDB: group management
// =============================================================================

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

// =============================================================================
// CoverPoint and bin management
// =============================================================================

CoverPoint* CoverageDB::AddCoverPoint(CoverGroup* group, std::string name) {
  group->coverpoints.push_back(CoverPoint{
      std::move(name), {}, false, true, 0, 0, group->options.auto_bin_max});
  return &group->coverpoints.back();
}

CoverBin* CoverageDB::AddBin(CoverPoint* cp, CoverBin bin) {
  cp->bins.push_back(std::move(bin));
  return &cp->bins.back();
}

// =============================================================================
// S19.5.1-19.5.3: Auto bin creation
// =============================================================================

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

// =============================================================================
// S19.6: Cross coverage
// =============================================================================

CrossCover* CoverageDB::AddCross(CoverGroup* group, CrossCover cross) {
  group->crosses.push_back(std::move(cross));
  return &group->crosses.back();
}

// =============================================================================
// S19.8: Sampling
// =============================================================================

void CoverageDB::SampleCoverPoint(CoverPoint* cp, int64_t value) {
  if (cp->has_iff_guard && !cp->iff_guard_value) return;
  for (auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIllegal) continue;
    if (bin.kind == CoverBinKind::kIgnore) continue;
    if (MatchesBin(bin, value)) {
      ++bin.hit_count;
    }
  }
}

void CoverageDB::SampleCross(
    CrossCover* cross,
    const std::vector<std::pair<std::string, int64_t>>& vals) {
  for (auto& cbin : cross->bins) {
    if (MatchesCrossBin(cbin, cross->coverpoint_names, vals)) {
      ++cbin.hit_count;
    }
  }
}

void CoverageDB::Sample(
    CoverGroup* group,
    const std::vector<std::pair<std::string, int64_t>>& values) {
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

// =============================================================================
// S19.8: Coverage computation
// =============================================================================

double CoverageDB::GetPointCoverage(const CoverPoint* cp) {
  if (cp->bins.empty()) return 100.0;
  uint32_t total = 0;
  uint32_t covered = 0;
  for (const auto& bin : cp->bins) {
    if (bin.kind == CoverBinKind::kIllegal) continue;
    if (bin.kind == CoverBinKind::kIgnore) continue;
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
  if (group->coverpoints.empty() && group->crosses.empty()) return 0.0;
  double sum = 0.0;
  uint32_t count = 0;
  for (const auto& cp : group->coverpoints) {
    sum += GetPointCoverage(&cp);
    ++count;
  }
  for (const auto& cross : group->crosses) {
    sum += GetCrossCoverage(&cross);
    ++count;
  }
  if (count == 0) return 0.0;
  return sum / static_cast<double>(count);
}

double CoverageDB::GetInstCoverage(const CoverGroup* group) {
  return GetCoverage(group);
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

}  // namespace delta
