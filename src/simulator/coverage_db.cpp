#include <algorithm>
#include <cstdint>
#include <deque>
#include <fstream>
#include <istream>
#include <ostream>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

namespace delta {

void CoverageDB::SetCoverageDbName(std::string filename) {
  coverage_db_name_ = std::move(filename);
}

const std::string& CoverageDB::CoverageDbName() const {
  return coverage_db_name_;
}

template <typename Bins>
static void AddBinCounts(Bins& into, const Bins& from, bool unite) {
  for (const auto& bin : from) {
    auto it = std::find_if(into.begin(), into.end(),
                           [&](const auto& b) { return b.name == bin.name; });
    if (it != into.end()) {
      it->hit_count += bin.hit_count;
    } else if (unite) {
      into.push_back(bin);
    }
  }
}

template <typename Items>
static void AddItemCounts(Items& into, const Items& from, bool unite) {
  for (const auto& item : from) {
    auto it = std::find_if(into.begin(), into.end(),
                           [&](const auto& i) { return i.name == item.name; });
    if (it != into.end()) {
      AddBinCounts(it->bins, item.bins, unite);
    } else if (unite) {
      into.push_back(item);
    }
  }
}

static void AddGroupCounts(CoverGroup& into, const CoverGroup& from,
                           bool unite) {
  AddItemCounts(into.coverpoints, from.coverpoints, unite);
  AddItemCounts(into.crosses, from.crosses, unite);
}

void CoverageDB::AddCumulativeCounts(CoverGroup& group,
                                     const CoverGroup& cumulative) {
  AddGroupCounts(group, cumulative, false);
}

void CoverageDB::MergeCumulativeCoverage(
    const std::vector<CoverGroup>& cumulative) {
  for (const CoverGroup& record : cumulative) {
    auto it = std::find_if(loaded_.begin(), loaded_.end(), [&](const auto& g) {
      return !record.type_name.empty() && g.type_name == record.type_name;
    });
    if (it == loaded_.end()) {
      loaded_.push_back(record);
      continue;
    }
    it->sample_count += record.sample_count;
    AddGroupCounts(*it, record, true);
  }
}

static bool ReadCrossDbRecord(std::istream& in, const std::string& tag,
                              std::vector<CoverGroup>& loaded) {
  if (loaded.empty()) return false;
  std::vector<CrossCover>& crosses = loaded.back().crosses;
  if (tag == "CR") {
    CrossCover cross;
    if (!(in >> cross.name)) return false;
    crosses.push_back(std::move(cross));
    return true;
  }
  if (crosses.empty()) return false;
  CrossBin b;
  if (!(in >> b.name >> b.hit_count)) return false;
  crosses.back().bins.push_back(std::move(b));
  return true;
}

static bool ReadGroupDbRecord(std::istream& in, const std::string& tag,
                              std::vector<CoverGroup>& loaded) {
  if (tag == "CG") {
    CoverGroup g;
    if (!(in >> g.name >> g.sample_count)) return false;
    loaded.push_back(std::move(g));
    return true;
  }
  if (loaded.empty()) return false;
  return static_cast<bool>(in >> loaded.back().type_name);
}

static bool ReadCoverageDbRecord(std::istream& in, const std::string& tag,
                                 std::vector<CoverGroup>& loaded) {
  if (tag == "CR" || tag == "XBIN") return ReadCrossDbRecord(in, tag, loaded);
  if (tag == "CG" || tag == "TY") return ReadGroupDbRecord(in, tag, loaded);
  if (tag == "CP") {
    if (loaded.empty()) return false;
    CoverPoint cp;
    if (!(in >> cp.name)) return false;
    loaded.back().coverpoints.push_back(std::move(cp));
    return true;
  }
  if (tag != "BIN") return false;
  if (loaded.empty() || loaded.back().coverpoints.empty()) return false;
  CoverBin b;
  int64_t value = 0;
  if (!(in >> b.name >> value >> b.hit_count)) return false;
  b.values.push_back(value);
  loaded.back().coverpoints.back().bins.push_back(std::move(b));
  return true;
}

bool CoverageDB::LoadCoverageDbFile(const std::string& path) {
  std::ifstream in(path);
  if (!in) return false;

  std::vector<CoverGroup> loaded;
  std::string tag;
  while (in >> tag) {
    if (!ReadCoverageDbRecord(in, tag, loaded)) return false;
  }

  MergeCumulativeCoverage(loaded);
  return true;
}

static void WriteGroupItems(std::ostream& out, const CoverGroup& g) {
  for (const CoverPoint& cp : g.coverpoints) {
    out << "CP " << cp.name << '\n';
    for (const CoverBin& b : cp.bins) {
      out << "BIN " << b.name << ' '
          << (b.values.empty() ? 0 : b.values.front()) << ' ' << b.hit_count
          << '\n';
    }
  }
  for (const CrossCover& cross : g.crosses) {
    out << "CR " << cross.name << '\n';
    for (const CrossBin& b : cross.bins) {
      out << "XBIN " << b.name << ' ' << b.hit_count << '\n';
    }
  }
}

static void WriteGroup(std::ostream& out, const CoverGroup& g) {
  out << "CG " << g.name << ' ' << g.sample_count << '\n';
  if (!g.type_name.empty()) out << "TY " << g.type_name << '\n';
  WriteGroupItems(out, g);
}

void CoverageDB::SaveCoverageDbFile(const std::string& path) const {
  std::ofstream out(path);
  for (const CoverGroup& g : groups_) WriteGroup(out, g);
  for (const CoverGroup& g : loaded_) WriteGroup(out, g);
}

const CoverGroup* CoverageDB::LoadedCoverageOf(
    std::string_view type_name) const {
  if (type_name.empty()) return nullptr;
  for (const CoverGroup& g : loaded_) {
    if (g.type_name == type_name) return &g;
  }
  return nullptr;
}

double CoverageDB::GetGlobalCoverage() const {
  std::deque<CoverGroup> terms(groups_.begin(), groups_.end());
  std::set<std::string_view> built;
  for (CoverGroup& g : terms) {
    const CoverGroup* cumulative = LoadedCoverageOf(g.type_name);
    if (cumulative != nullptr) AddCumulativeCounts(g, *cumulative);
    built.insert(g.type_name);
  }
  for (const CoverGroup& g : loaded_) {
    if (g.type_name.empty() || !built.contains(g.type_name)) terms.push_back(g);
  }
  std::vector<const CoverGroup*> instances;
  instances.reserve(terms.size());
  for (const CoverGroup& g : terms) instances.push_back(&g);
  return ComputeOverallCoverage(instances);
}

void CoverageDB::SaveNamedCoverageDb() const {
  if (!coverage_db_name_.empty()) SaveCoverageDbFile(coverage_db_name_);
}

bool CoverageDB::CovergroupCoverageDenominatorZero(const CoverGroup* group) {
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
  double numerator = 0.0;
  int64_t denominator = 0;
  for (const CoverGroup* g : instances) {
    if (CovergroupCoverageDenominatorZero(g)) continue;
    numerator += GetCoverage(g) * static_cast<double>(g->options.weight);
    denominator += g->options.weight;
  }
  if (denominator == 0) return 100.0;
  return numerator / static_cast<double>(denominator);
}

void CoverageDB::ApplyDerivedCoverpointOverrides(
    CoverGroup* base,
    const std::vector<std::string>& derived_coverpoint_names) {
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
  for (CrossCover& cross : base->crosses) {
    if (std::find(derived_cross_names.begin(), derived_cross_names.end(),
                  cross.name) != derived_cross_names.end()) {
      cross.excluded_from_coverage = true;
    }
  }
}

bool CoverageDB::CovergroupTypesAggregate(std::string_view type_a,
                                          std::string_view type_b) {
  return type_a == type_b;
}

}  // namespace delta
