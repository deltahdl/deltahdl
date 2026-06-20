#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// LRM 19.5.1.1: a "with" expression keeps only the candidate values for which
// the expression (over "item") is true, preserving order.
TEST(CoverageWith, FiltersCandidatesByPredicate) {
  std::vector<int64_t> candidates;
  for (int64_t v = 0; v <= 255; ++v) candidates.push_back(v);

  auto selected = CoverageDB::ApplyWithExpression(
      candidates, [](int64_t item) { return item % 3 == 0; });

  ASSERT_FALSE(selected.empty());
  EXPECT_EQ(selected.front(), 0);
  EXPECT_EQ(selected[1], 3);
  EXPECT_EQ(selected[2], 6);
  for (int64_t v : selected) EXPECT_EQ(v % 3, 0);
}

// LRM 19.5.1.1: the result of applying the with expression preserves duplicate
// values as well as the original ordering of the candidate list.
TEST(CoverageWith, PreservesOrderAndDuplicates) {
  std::vector<int64_t> candidates = {7, 4, 4, 1, 8, 4};

  auto selected = CoverageDB::ApplyWithExpression(
      candidates, [](int64_t item) { return item % 2 == 0; });

  std::vector<int64_t> expected = {4, 4, 8, 4};
  EXPECT_EQ(selected, expected);
}

// LRM 19.5.1.1: a with bin filter is not allowed on a coverpoint of a real
// type, but is allowed on an integral coverpoint.
TEST(CoverageWith, RejectedOnRealCoverpoint) {
  CoverPoint integral_cp;
  integral_cp.is_real = false;
  EXPECT_TRUE(CoverageDB::WithExpressionAllowed(&integral_cp));

  CoverPoint real_cp;
  real_cp.is_real = true;
  EXPECT_FALSE(CoverageDB::WithExpressionAllowed(&real_cp));
}

// LRM 19.5.1.1: in place of a range list a with expression may name only the
// enclosing coverpoint; no other coverpoint name is permitted.
TEST(CoverageWith, RangeReferenceMustNameOwnCoverpoint) {
  EXPECT_TRUE(CoverageDB::WithRangeReferenceAllowed("a", "a"));
  EXPECT_FALSE(CoverageDB::WithRangeReferenceAllowed("a", "b"));
}

// LRM 19.5.1.1 / LRM 19.7.1: by default the with filter runs before values are
// distributed into bins; the distribute_first type option distributes first
// and then filters the contents of each bin, which yields a different layout.
TEST(CoverageWith, DistributeFirstChangesOrdering) {
  std::vector<int64_t> candidates = {0, 1, 2, 3, 4, 5, 6, 7};
  auto small = [](int64_t item) { return item < 3; };

  auto filter_first =
      CoverageDB::ApplyWithAndDistribute(candidates, small, 2,
                                         /*distribute_first=*/false);
  // Survivors {0,1,2} split across 2 bins, last bin takes the remainder.
  ASSERT_EQ(filter_first.size(), 2u);
  EXPECT_EQ(filter_first[0], (std::vector<int64_t>{0}));
  EXPECT_EQ(filter_first[1], (std::vector<int64_t>{1, 2}));

  auto distribute_first =
      CoverageDB::ApplyWithAndDistribute(candidates, small, 2,
                                         /*distribute_first=*/true);
  // Eight values split first into {0,1,2,3},{4,5,6,7}, then each bin filtered.
  ASSERT_EQ(distribute_first.size(), 2u);
  EXPECT_EQ(distribute_first[0], (std::vector<int64_t>{0, 1, 2}));
  EXPECT_TRUE(distribute_first[1].empty());

  EXPECT_NE(filter_first, distribute_first);
}

// LRM 19.5.1.1 (edge case): a with expression that no candidate satisfies
// produces an empty selection.
TEST(CoverageWith, EmptyWhenNoCandidateMatches) {
  std::vector<int64_t> candidates = {1, 3, 5, 7};
  auto selected = CoverageDB::ApplyWithExpression(
      candidates, [](int64_t item) { return item % 2 == 0; });
  EXPECT_TRUE(selected.empty());
}

// LRM 19.5.1.1 (edge case): distributing the filtered values into zero bins
// yields no bins.
TEST(CoverageWith, DistributeIntoZeroBins) {
  std::vector<int64_t> candidates = {0, 1, 2, 3};
  auto bins = CoverageDB::ApplyWithAndDistribute(
      candidates, [](int64_t) { return true; }, /*num_bins=*/0,
      /*distribute_first=*/false);
  EXPECT_TRUE(bins.empty());
}

}  // namespace
