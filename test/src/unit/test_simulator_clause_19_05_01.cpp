#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, ExplicitBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin bin;
  bin.name = "low";
  bin.kind = CoverBinKind::kExplicit;
  bin.values = {0, 1, 2, 3};
  auto* b = CoverageDB::AddBin(cp, bin);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->name, "low");
  EXPECT_EQ(b->values.size(), 4u);
}

TEST(Coverage, SampleHitsExplicitBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "val");
  CoverBin bin;
  bin.name = "ones";
  bin.values = {1};
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"val", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

TEST(Coverage, AutoBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 7);
  EXPECT_EQ(cp->bins.size(), 4u);

  struct {
    size_t bin_idx;
    size_t val_idx;
    int64_t expected;
  } const kCases[] = {
      {0, 0, 0},
      {0, 1, 1},
      {3, 0, 6},
      {3, 1, 7},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(cp->bins[c.bin_idx].values[c.val_idx], c.expected);
  }
  EXPECT_EQ(cp->bins[0].values.size(), 2u);
}

TEST(Coverage, AutoBinSmallRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  EXPECT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].values.size(), 1u);
  EXPECT_EQ(cp->bins[0].values[0], 0);
}

// LRM 19.5.1: a fixed number of bins smaller than the value count distributes
// the values uniformly. For bins fixed[4] = {[1:10], 1, 4, 7} there are 13
// values and B = 13/4 = 3, giving <1,2,3>,<4,5,6>,<7,8,9>,<10,1,4,7>.
TEST(Coverage, IntegralFixedBinDistribution) {
  std::vector<int64_t> values;
  for (int64_t v = 1; v <= 10; ++v) values.push_back(v);
  values.push_back(1);
  values.push_back(4);
  values.push_back(7);

  auto bins = CoverageDB::DistributeValues(values, 4);
  ASSERT_EQ(bins.size(), 4u);
  EXPECT_EQ(bins[0], (std::vector<int64_t>{1, 2, 3}));
  EXPECT_EQ(bins[1], (std::vector<int64_t>{4, 5, 6}));
  EXPECT_EQ(bins[2], (std::vector<int64_t>{7, 8, 9}));
  // The last bin absorbs the remaining values; duplicates are retained.
  EXPECT_EQ(bins[3], (std::vector<int64_t>{10, 1, 4, 7}));
}

// LRM 19.5.1: when the number of bins exceeds the number of values, the surplus
// bins stay empty. For bins fixed[5] = {1, 4, 7}: <1>,<4>,<7>,<>,<>.
TEST(Coverage, IntegralFixedBinMoreBinsThanValues) {
  auto bins = CoverageDB::DistributeValues({1, 4, 7}, 5);
  ASSERT_EQ(bins.size(), 5u);
  EXPECT_EQ(bins[0], (std::vector<int64_t>{1}));
  EXPECT_EQ(bins[1], (std::vector<int64_t>{4}));
  EXPECT_EQ(bins[2], (std::vector<int64_t>{7}));
  EXPECT_TRUE(bins[3].empty());
  EXPECT_TRUE(bins[4].empty());
}

// LRM 19.5.1: the same distribution covers a real coverpoint, whose items are
// the intervals of its ranges plus its individual values. bins fixed[4] over 9
// items gives B = 2 and groups <0,1>,<2,3>,<4,5>,<6,7,8>.
TEST(Coverage, RealFixedBinItemDistribution) {
  std::vector<int64_t> items{0, 1, 2, 3, 4, 5, 6, 7, 8};
  auto bins = CoverageDB::DistributeValues(items, 4);
  ASSERT_EQ(bins.size(), 4u);
  EXPECT_EQ(bins[0], (std::vector<int64_t>{0, 1}));
  EXPECT_EQ(bins[1], (std::vector<int64_t>{2, 3}));
  EXPECT_EQ(bins[2], (std::vector<int64_t>{4, 5}));
  EXPECT_EQ(bins[3], (std::vector<int64_t>{6, 7, 8}));
}

// LRM 19.5.1: state bins of an open array "name[]" are named "name[value]";
// state bins of a sized array "name[N]" are named "name[0]" through
// "name[N-1]".
TEST(Coverage, StateBinNaming) {
  EXPECT_EQ(CoverageDB::StateBinName("c", 200), "c[200]");
  EXPECT_EQ(CoverageDB::StateBinName("c", 202), "c[202]");
  EXPECT_EQ(CoverageDB::StateBinName("d", 0), "d[0]");
  EXPECT_EQ(CoverageDB::StateBinName("d", 7), "d[7]");
}

// LRM 19.5.1: an open array "name[]" creates a separate bin for each distinct
// value of the range list, named "name[value]". For c[] = {200, 201, 202}
// there are three bins c[200], c[201], c[202].
TEST(Coverage, IntegralOpenArrayBins) {
  auto bins = CoverageDB::OpenArrayValueBins("c", {200, 201, 202});
  ASSERT_EQ(bins.size(), 3u);
  EXPECT_EQ(bins[0].name, "c[200]");
  EXPECT_EQ(bins[1].name, "c[201]");
  EXPECT_EQ(bins[2].name, "c[202]");
  EXPECT_EQ(bins[0].values, (std::vector<int64_t>{200}));
}

// LRM 19.5.1: a value listed more than once (here through overlapping ranges
// [127:150] and [148:191]) is still given exactly one bin, so the open array
// holds one bin per distinct value: b[127] through b[191], i.e. 65 bins.
TEST(Coverage, IntegralOpenArrayDedupesOverlap) {
  std::vector<int64_t> values;
  for (int64_t v = 127; v <= 150; ++v) values.push_back(v);
  for (int64_t v = 148; v <= 191; ++v) values.push_back(v);

  auto bins = CoverageDB::OpenArrayValueBins("b", values);
  ASSERT_EQ(bins.size(), 65u);
  EXPECT_EQ(bins.front().name, "b[127]");
  EXPECT_EQ(bins.back().name, "b[191]");
}

// LRM 19.5.1: a real range wider than one interval is split into interval-size
// partitions, each inclusive of its low and exclusive of its high, except the
// last, which is inclusive of its high too.
TEST(Coverage, RealRangeDividedIntoIntervals) {
  auto ivs = CoverageDB::RealRangeIntervals(1.0, 4.0, 1.0, false);
  ASSERT_EQ(ivs.size(), 3u);
  EXPECT_NEAR(ivs[0].low, 1.0, 1e-9);
  EXPECT_NEAR(ivs[0].high, 2.0, 1e-9);
  EXPECT_FALSE(ivs[0].high_inclusive);
  EXPECT_NEAR(ivs[1].low, 2.0, 1e-9);
  EXPECT_NEAR(ivs[1].high, 3.0, 1e-9);
  EXPECT_FALSE(ivs[1].high_inclusive);
  EXPECT_NEAR(ivs[2].low, 3.0, 1e-9);
  EXPECT_NEAR(ivs[2].high, 4.0, 1e-9);
  EXPECT_TRUE(ivs[2].high_inclusive);
}

// LRM 19.5.1: a range no wider than the interval is a single bin covering the
// whole range inclusively; when the range is not evenly divisible the last
// partition is shorter and inclusive of high.
TEST(Coverage, RealRangeIntervalEdgeCases) {
  auto exact = CoverageDB::RealRangeIntervals(1.0, 2.0, 1.0, false);
  ASSERT_EQ(exact.size(), 1u);
  EXPECT_TRUE(exact[0].high_inclusive);

  auto uneven = CoverageDB::RealRangeIntervals(1.0, 2.5, 1.0, false);
  ASSERT_EQ(uneven.size(), 2u);
  EXPECT_NEAR(uneven[1].low, 2.0, 1e-9);
  EXPECT_NEAR(uneven[1].high, 2.5, 1e-9);
  EXPECT_TRUE(uneven[1].high_inclusive);
}

// LRM 19.5.1: a real range bounded with the $ primary is one undivided bin,
// while an equally wide ordinary range divides into several.
TEST(Coverage, RealDollarRangeIsSingleBin) {
  auto dollar = CoverageDB::RealRangeIntervals(0.75, 100.0, 1.0, true);
  EXPECT_EQ(dollar.size(), 1u);

  auto ordinary = CoverageDB::RealRangeIntervals(0.75, 100.0, 1.0, false);
  EXPECT_GT(ordinary.size(), 1u);
}

// LRM 19.5.1: real interval bins name their endpoints with "[" / "]" for an
// inclusive bound and ")" for an exclusive one; an individual value bin is
// named "name[value]".
TEST(Coverage, RealBinNaming) {
  EXPECT_EQ(CoverageDB::RealIntervalBinName("a2", {1.0, 2.0, false}),
            "a2[1.0:2.0)");
  EXPECT_EQ(CoverageDB::RealIntervalBinName("a2", {2.0, 3.0, true}),
            "a2[2.0:3.0]");
  EXPECT_EQ(CoverageDB::RealIntervalBinName("a2", {8.4, 8.6, true}),
            "a2[8.4:8.6]");
  EXPECT_EQ(CoverageDB::RealValueBinName("a2", 7.5), "a2[7.5]");
}

// LRM 19.5.1: when an open real bin array spans several ranges, exactly
// identical intervals merge, but intervals that share endpoints yet differ in
// inclusivity are kept separate.
TEST(Coverage, RealIdenticalIntervalsMerged) {
  std::vector<RealInterval> intervals{
      {2.0, 3.0, false},  // from one range
      {2.0, 3.0, false},  // identical -> merged away
      {3.0, 4.0, false},  // exclusive high
      {3.0, 4.0, true},   // inclusive high -> kept separate
  };
  auto merged = CoverageDB::MergeIdenticalIntervals(intervals);
  ASSERT_EQ(merged.size(), 3u);
  EXPECT_FALSE(merged[1].high_inclusive);
  EXPECT_TRUE(merged[2].high_inclusive);
}

// LRM 19.5.1: a default bin for a real coverpoint may not be declared as an
// array of bins.
TEST(Coverage, RealDefaultBinCannotBeArray) {
  EXPECT_FALSE(CoverageDB::RealDefaultBinMayBeArray());
}

// LRM 19.5.1: a trailing iff guard on a bin definition suppresses that bin's
// increment when the guard is false at the sampling point.
TEST(Coverage, PerBinIffGuard) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "guarded";
  bin.values = {5};
  bin.has_iff_guard = true;
  bin.iff_guard_value = false;
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 5}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);

  g->coverpoints[0].bins[0].iff_guard_value = true;
  db.Sample(g, {{"v", 5}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

}  // namespace
