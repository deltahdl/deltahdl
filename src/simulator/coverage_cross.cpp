#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_internal.h"
#include "simulator/coverage_types.h"

namespace delta {

void CoverageDB::EnsureCrossCoverPoints(CoverGroup* group,
                                        const std::vector<std::string>& names) {
  for (const auto& name : names) {
    bool found = false;
    for (const auto& cp : group->coverpoints) {
      if (cp.name == name) {
        found = true;
        break;
      }
    }
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

namespace {

std::vector<size_t> ContributingBins(const CoverGroup& group,
                                     const std::string& name) {
  std::vector<size_t> contributing;
  for (const auto& cp : group.coverpoints) {
    if (cp.name != name) continue;
    for (size_t i = 0; i < cp.bins.size(); ++i) {
      CoverBinKind kind = cp.bins[i].kind;
      if (kind == CoverBinKind::kDefault ||
          kind == CoverBinKind::kDefaultSequence ||
          kind == CoverBinKind::kIgnore || kind == CoverBinKind::kIllegal) {
        continue;
      }
      contributing.push_back(i);
    }
    break;
  }
  return contributing;
}

}  // namespace

std::vector<std::vector<size_t>> CoverageDB::CrossProductTuples(
    const CoverGroup* group, const CrossCover* cross) {
  std::vector<std::vector<size_t>> per_point;
  per_point.reserve(cross->coverpoint_names.size());
  std::vector<size_t> counts;
  counts.reserve(cross->coverpoint_names.size());
  for (const auto& name : cross->coverpoint_names) {
    per_point.push_back(ContributingBins(*group, name));
    counts.push_back(per_point.back().size());
  }
  std::vector<std::vector<size_t>> tuples = EnumerateCrossProducts(counts);
  for (auto& tuple : tuples) {
    for (size_t i = 0; i < tuple.size(); ++i) tuple[i] = per_point[i][tuple[i]];
  }
  return tuples;
}

std::string CoverageDB::CrossProductName(const CoverGroup* group,
                                         const CrossCover* cross,
                                         const std::vector<size_t>& tuple) {
  std::string name = "<";
  for (size_t i = 0; i < tuple.size(); ++i) {
    if (i != 0) name += ",";
    for (const auto& cp : group->coverpoints) {
      if (cp.name == cross->coverpoint_names[i]) {
        name += cp.bins[tuple[i]].name;
        break;
      }
    }
  }
  return name + ">";
}

void CoverageDB::AutoCreateCrossBins(CoverGroup* group, CrossCover* cross) {
  cross->bins.clear();
  for (auto& tuple : CrossProductTuples(group, cross)) {
    CrossBin cbin;
    cbin.name = CrossProductName(group, cross, tuple);
    cbin.bin_tuples.push_back(std::move(tuple));
    cross->bins.push_back(std::move(cbin));
  }
}

bool CoverageDB::CrossBareVariableAllowed(bool variable_is_real) {
  return !variable_is_real;
}

std::vector<int64_t> CoverageDB::BinsofBinValues(const CoverBin& bin) {
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
    if (static_cast<size_t>(bin_index) < cp->bins.size()) {
      yielded.push_back(
          BinsofBinValues(cp->bins[static_cast<size_t>(bin_index)]));
    }
    return yielded;
  }
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
    if (std::find(user_selected_products.begin(), user_selected_products.end(),
                  product) == user_selected_products.end()) {
      retained.push_back(product);
    }
  }
  return retained;
}

namespace {

bool ValueSetsYieldAnyTuple(
    const std::vector<std::vector<int64_t>>& bin_tuple_value_sets) {
  if (bin_tuple_value_sets.empty()) return false;
  for (const auto& values : bin_tuple_value_sets) {
    if (values.empty()) return false;
  }
  return true;
}

bool AdvanceValueTupleIndex(
    const std::vector<std::vector<int64_t>>& bin_tuple_value_sets,
    std::vector<size_t>& idx) {
  size_t pos = bin_tuple_value_sets.size();
  while (true) {
    --pos;
    if (++idx[pos] < bin_tuple_value_sets[pos].size()) return true;
    idx[pos] = 0;
    if (pos == 0) return false;
  }
}

}  // namespace

uint64_t CoverageDB::CountSatisfyingValueTuples(
    const std::vector<std::vector<int64_t>>& bin_tuple_value_sets,
    const std::function<bool(const std::vector<int64_t>&)>& pred) {
  if (!ValueSetsYieldAnyTuple(bin_tuple_value_sets)) return 0;
  uint64_t satisfying = 0;
  std::vector<size_t> idx(bin_tuple_value_sets.size(), 0);
  std::vector<int64_t> tuple(bin_tuple_value_sets.size());
  while (true) {
    for (size_t i = 0; i < bin_tuple_value_sets.size(); ++i) {
      tuple[i] = bin_tuple_value_sets[i][idx[i]];
    }
    if (pred(tuple)) ++satisfying;
    if (!AdvanceValueTupleIndex(bin_tuple_value_sets, idx)) return satisfying;
  }
}

std::vector<size_t> CoverageDB::SelectCrossBinTuples(
    const std::vector<std::vector<std::vector<int64_t>>>& candidate_bin_tuples,
    const std::function<bool(const std::vector<int64_t>&)>* pred,
    const CrossWithMatchPolicy& policy) {
  std::vector<size_t> selected;
  for (size_t c = 0; c < candidate_bin_tuples.size(); ++c) {
    if (pred == nullptr) {
      selected.push_back(c);
      continue;
    }
    const auto& sets = candidate_bin_tuples[c];
    uint64_t satisfying = CountSatisfyingValueTuples(sets, *pred);
    bool keep = false;
    if (policy.require_all) {
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

std::vector<size_t> CoverageDB::SelectCrossBinTuplesBySetExpression(
    const std::vector<std::vector<std::vector<int64_t>>>& candidate_bin_tuples,
    const std::vector<std::vector<int64_t>>& set_expression_elements,
    const CrossWithMatchPolicy& policy) {
  std::function<bool(const std::vector<int64_t>&)> present =
      [&set_expression_elements](const std::vector<int64_t>& tuple) {
        return std::find(set_expression_elements.begin(),
                         set_expression_elements.end(),
                         tuple) != set_expression_elements.end();
      };
  return SelectCrossBinTuples(candidate_bin_tuples, &present, policy);
}

std::vector<std::vector<size_t>> CoverageDB::ExcludeIgnoredCrossProducts(
    const std::vector<std::vector<size_t>>& products,
    const std::vector<std::vector<size_t>>& ignored) {
  std::vector<std::vector<size_t>> kept;
  for (const auto& product : products) {
    if (std::find(ignored.begin(), ignored.end(), product) == ignored.end()) {
      kept.push_back(product);
    }
  }
  return kept;
}

bool CoverageDB::IgnoredCrossProductRetained(bool) { return false; }

std::vector<std::vector<size_t>> CoverageDB::ExcludeIllegalCrossProducts(
    const std::vector<std::vector<size_t>>& products,
    const std::vector<std::vector<size_t>>& illegal) {
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
    const std::vector<std::vector<size_t>>& ignored, bool) {
  if (std::find(illegal.begin(), illegal.end(), product) != illegal.end()) {
    return CrossSampleOutcome::kIllegalError;
  }
  if (std::find(ignored.begin(), ignored.end(), product) != ignored.end()) {
    return CrossSampleOutcome::kIgnored;
  }
  return CrossSampleOutcome::kCounted;
}

static void ReportMissingBinsOf(const CoverGroup& group,
                                const CrossCover& cross, std::ostream& os) {
  std::vector<const CrossBin*> missing;
  for (const CrossBin& bin : cross.bins) {
    if (bin.hit_count < bin.at_least) missing.push_back(&bin);
  }
  if (missing.empty()) return;
  os << "cross " << group.name << "." << cross.name << ": " << missing.size()
     << " cross bins missing\n";
  size_t shown =
      std::min(missing.size(),
               static_cast<size_t>(cross.option.cross_num_print_missing));
  for (size_t i = 0; i < shown; ++i) os << "  " << missing[i]->name << "\n";
}

void CoverageDB::ReportMissingCrossBins(std::ostream& os) const {
  for (const CoverGroup& group : groups_) {
    for (const CrossCover& cross : group.crosses) {
      if (cross.option.cross_num_print_missing > 0) {
        ReportMissingBinsOf(group, cross, os);
      }
    }
  }
}

}  // namespace delta
