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

// --- LRM 19.9: predefined coverage system tasks and system functions --------

void CoverageDB::SetCoverageDbName(std::string filename) {
  coverage_db_name_ = std::move(filename);
}

const std::string& CoverageDB::CoverageDbName() const {
  return coverage_db_name_;
}

// Adds the hit counts of `from`'s bins to `into`'s of the same name and, where
// `unite` is set, appends the bins `into` lacks (LRM 19.11.3).
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

// AddBinCounts applied to each coverpoint or cross of `from` and that of
// `into` of the same name; where `unite` is set, the items `into` lacks are
// appended.
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

// Read a cross record of a coverage snapshot, "CR <name>" opening a cross of
// the last covergroup and "XBIN <name> <hit_count>" a bin of the last cross,
// into the parsed record list.
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

// Read an instance record of a coverage snapshot, "CG <name> <sample_count>"
// opening a covergroup instance and "TY <name>" naming the covergroup type of
// the last one, into the parsed record list.
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

// Read one record of a coverage snapshot into the parsed record list. A record
// tag the format does not define, or one whose enclosing record is missing (a
// coverpoint or bin outside a covergroup), fails the read.
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

  // Parse the snapshot into standalone covergroup records; a malformed token
  // ordering (a coverpoint or bin with no enclosing record) aborts the load
  // before it touches the live database.
  std::vector<CoverGroup> loaded;
  std::string tag;
  while (in >> tag) {
    if (!ReadCoverageDbRecord(in, tag, loaded)) return false;
  }

  MergeCumulativeCoverage(loaded);
  return true;
}

// Writes the coverpoints and crosses of one covergroup instance, each with its
// bins, in the form LoadCoverageDbFile reads.
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

// Writes one covergroup instance record, its type and its items.
static void WriteGroup(std::ostream& out, const CoverGroup& g) {
  out << "CG " << g.name << ' ' << g.sample_count << '\n';
  if (!g.type_name.empty()) out << "TY " << g.type_name << '\n';
  WriteGroupItems(out, g);
}

// The run's own instances, then the records a load brought, so the cumulative
// coverage a later run loads keeps every earlier run's (LRM 19.9).
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
  // $get_coverage reports the overall coverage of all covergroup types as the
  // weighted average of their per-covergroup coverage. Per LRM 19.11, a
  // covergroup whose own denominator is zero does not contribute to the overall
  // score (it is dropped from both the numerator and the denominator), and a
  // design with no contributing covergroups — none exist, or every covergroup
  // has a weight of zero — reports 100.0. ComputeOverallCoverage applies
  // exactly those rules, so $get_coverage routes through it.
  // The cumulative coverage loaded for a type adds its bin counts to each
  // instance of it the run built (LRM 19.9, 19.11.1), and stands in for the
  // type where the run built none.
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
