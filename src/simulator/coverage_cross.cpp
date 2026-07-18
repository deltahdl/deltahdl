#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_internal.h"

namespace delta {

// --- LRM 19.6: cross coverage -----------------------------------------------

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

namespace {

// Collects, for one crossed coverpoint name, the value lists of the bins that
// may contribute a cross product. Default, ignore, and illegal bins are skipped
// (LRM 19.6). Returns an empty list when the coverpoint is absent.
std::vector<std::vector<int64_t>> CollectContributingBinValues(
    CoverGroup* group, const std::string& name) {
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
  return contributing;
}

// Builds one cross bin from the current per-coverpoint bin index combination.
CrossBin MakeCrossProductBin(
    const std::vector<std::vector<std::vector<int64_t>>>& per_point,
    const std::vector<size_t>& idx) {
  CrossBin cbin;
  cbin.value_sets.reserve(per_point.size());
  cbin.name = "<";
  for (size_t i = 0; i < per_point.size(); ++i) {
    cbin.value_sets.push_back(per_point[i][idx[i]]);
    if (i != 0) cbin.name += ",";
    cbin.name += std::to_string(idx[i]);
  }
  cbin.name += ">";
  return cbin;
}

// Advances the per-coverpoint bin index combination to the next Cartesian
// product position. Returns false when the product has been exhausted.
bool AdvanceCrossProductIndex(
    const std::vector<std::vector<std::vector<int64_t>>>& per_point,
    std::vector<size_t>& idx) {
  size_t pos = per_point.size();
  while (pos > 0) {
    --pos;
    if (++idx[pos] < per_point[pos].size()) return true;
    idx[pos] = 0;
    if (pos == 0) return false;
  }
  return false;
}

}  // namespace

void CoverageDB::AutoCreateCrossBins(CoverGroup* group, CrossCover* cross) {
  // Collect, for each crossed coverpoint, the value lists of the bins that may
  // contribute a cross product. Default, ignore, and illegal bins are skipped
  // (LRM 19.6).
  std::vector<std::vector<std::vector<int64_t>>> per_point;
  per_point.reserve(cross->coverpoint_names.size());
  for (const auto& name : cross->coverpoint_names) {
    per_point.push_back(CollectContributingBinValues(group, name));
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
    cross->bins.push_back(MakeCrossProductBin(per_point, idx));
    if (!AdvanceCrossProductIndex(per_point, idx)) return;
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
      yielded.push_back(
          BinsofBinValues(cp->bins[static_cast<size_t>(bin_index)]));
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
    if (std::find(user_selected_products.begin(), user_selected_products.end(),
                  product) == user_selected_products.end()) {
      retained.push_back(product);
    }
  }
  return retained;
}

// --- LRM 19.6.1.2: cross bin with covergroup expressions --------------------

namespace {

// True when the value-set list produces at least one value tuple: it must be
// non-empty and every coverpoint must contribute at least one value.
bool ValueSetsYieldAnyTuple(
    const std::vector<std::vector<int64_t>>& bin_tuple_value_sets) {
  if (bin_tuple_value_sets.empty()) return false;
  for (const auto& values : bin_tuple_value_sets) {
    if (values.empty()) return false;
  }
  return true;
}

// Advances the per-coverpoint value index combination to the next value tuple.
// Returns false when every tuple has been visited.
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
  // No coverpoints, or any coverpoint with an empty value set, yields no value
  // tuples, hence nothing can satisfy the expression.
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
    // A bare cross_identifier (no with clause) keeps every candidate bin tuple.
    if (pred == nullptr) {
      selected.push_back(c);
      continue;
    }
    const auto& sets = candidate_bin_tuples[c];
    uint64_t satisfying = CountSatisfyingValueTuples(sets, *pred);
    bool keep = false;
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

std::vector<size_t> CoverageDB::SelectCrossBinTuplesBySetExpression(
    const std::vector<std::vector<std::vector<int64_t>>>& candidate_bin_tuples,
    const std::vector<std::vector<int64_t>>& set_expression_elements,
    const CrossWithMatchPolicy& policy) {
  // LRM 19.6.1.4: the cross_set_expression is a queue of value tuples; a
  // candidate bin tuple is selected by how many of its value tuples are present
  // as elements of that queue, under the same matches policy as the with
  // covergroup expression (LRM 19.6.1.2). Membership of a value tuple in the
  // queue is the per-value-tuple predicate the shared policy machinery counts.
  std::function<bool(const std::vector<int64_t>&)> present =
      [&set_expression_elements](const std::vector<int64_t>& tuple) {
        return std::find(set_expression_elements.begin(),
                         set_expression_elements.end(),
                         tuple) != set_expression_elements.end();
      };
  return SelectCrossBinTuples(candidate_bin_tuples, &present, policy);
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

}  // namespace delta
