#include <algorithm>
#include <cstdint>
#include <fstream>
#include <string>
#include <vector>

#include "simulator/coverage.h"

namespace delta {

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

// Accumulates one loaded cross onto a live cross of the same name, mirroring
// the per-bin accumulation used for coverpoints (LRM 19.9).
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

// Copies a covergroup seen only in the persisted database onto a freshly
// created live group in full (LRM 19.9).
static void CopyLoadedGroupInFull(CoverGroup* live, const CoverGroup& loaded) {
  live->coverpoints = loaded.coverpoints;
  live->crosses = loaded.crosses;
  live->options = loaded.options;
  live->type_option = loaded.type_option;
  live->collecting = loaded.collecting;
  live->sample_count = loaded.sample_count;
}

// Accumulates the loaded coverpoints onto the live group: a coverpoint matched
// by name accumulates per-bin counts, otherwise it is appended (LRM 19.9).
static void MergeLoadedGroupCoverPoints(CoverGroup* live,
                                        const CoverGroup& loaded) {
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
}

// Accumulates the loaded crosses onto the live group, mirroring the per-cross
// accumulation used for coverpoints (LRM 19.9).
static void MergeLoadedGroupCrosses(CoverGroup* live,
                                    const CoverGroup& loaded) {
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

void CoverageDB::MergeCumulativeCoverage(
    const std::vector<CoverGroup>& cumulative) {
  for (const auto& loaded : cumulative) {
    CoverGroup* live = FindGroup(loaded.name);
    if (live == nullptr) {
      // A covergroup type seen only in the persisted database is added in full.
      live = CreateGroup(loaded.name);
      CopyLoadedGroupInFull(live, loaded);
      continue;
    }

    // The loaded coverage is cumulative, so its counts add to the live ones.
    live->sample_count += loaded.sample_count;
    MergeLoadedGroupCoverPoints(live, loaded);
    MergeLoadedGroupCrosses(live, loaded);
  }
}

bool CoverageDB::LoadCoverageDbFile(const std::string& path) {
  std::ifstream in(path);
  if (!in) return false;

  // Parse the snapshot into standalone covergroup records; a malformed token
  // ordering (a coverpoint or bin with no enclosing record) aborts the load
  // before it touches the live database.
  std::vector<CoverGroup> loaded;
  std::string tag;
  while (in >> tag) {
    if (tag == "CG") {
      CoverGroup g;
      if (!(in >> g.name >> g.sample_count)) return false;
      loaded.push_back(std::move(g));
    } else if (tag == "CP") {
      if (loaded.empty()) return false;
      CoverPoint cp;
      if (!(in >> cp.name)) return false;
      loaded.back().coverpoints.push_back(std::move(cp));
    } else if (tag == "BIN") {
      if (loaded.empty() || loaded.back().coverpoints.empty()) return false;
      CoverBin b;
      int64_t value = 0;
      if (!(in >> b.name >> value >> b.hit_count)) return false;
      b.values.push_back(value);
      loaded.back().coverpoints.back().bins.push_back(std::move(b));
    } else {
      return false;  // Unrecognized record tag.
    }
  }

  MergeCumulativeCoverage(loaded);
  return true;
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

// --- LRM 19.4.1: embedded covergroup inheritance ----------------------------

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
  // LRM 19.4.1: a base cross stops contributing only when the derived
  // covergroup defines a cross with the same name. A base cross whose
  // coverpoint was overridden still contributes as long as no derived cross
  // shares its name.
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

}  // namespace delta
