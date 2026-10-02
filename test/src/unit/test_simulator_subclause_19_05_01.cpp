#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

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
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 1}}));
  EXPECT_EQ(cp->bins[3].ranges, (std::vector<CoverValueRange>{{6, 7}}));
}

TEST(Coverage, AutoBinSmallRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  EXPECT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 0}}));
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

// LRM 19.5.1: the +/- token is an absolute tolerance, so a single real value
// with it defines the range [value-tol, value+tol]. For {[ZSTATE+/-0.1]} with
// ZSTATE = -100.0 the bin covers -100.1..-99.9.
TEST(Coverage, AbsoluteToleranceDefinesRange) {
  auto range = CoverageDB::ToleranceRange(-100.0, 0.1, /*is_percent=*/false);
  EXPECT_NEAR(range.first, -100.1, 1e-9);
  EXPECT_NEAR(range.second, -99.9, 1e-9);
}

// LRM 19.5.1: the +%- token is a relative tolerance expressed as a percentage
// of the value's magnitude. For {[XSTATE%-1.0]} with XSTATE cast to 100.0 the
// ±1.0% tolerance covers 99.0..101.0.
TEST(Coverage, RelativeToleranceDefinesRange) {
  auto range = CoverageDB::ToleranceRange(100.0, 1.0, /*is_percent=*/true);
  EXPECT_NEAR(range.first, 99.0, 1e-9);
  EXPECT_NEAR(range.second, 101.0, 1e-9);
}

// LRM 19.5.1: a tolerance defines a range, so the range/interval rules apply. A
// tolerance range no wider than the real interval stays a single bin, while one
// wider than the interval is divided into multiple bins. The absolute range of
// {[ZSTATE+/-0.1]} (width 0.2) is one interval; the relative range of
// {[XSTATE%-1.0]} (width 2.0) divides into intervals of the default size 1.0.
TEST(Coverage, ToleranceRangeObeysIntervalDivision) {
  auto narrow = CoverageDB::ToleranceRange(-100.0, 0.1, /*is_percent=*/false);
  auto narrow_ivs = CoverageDB::RealRangeIntervals(
      narrow.first, narrow.second, /*interval=*/1.0, /*uses_dollar=*/false);
  EXPECT_EQ(narrow_ivs.size(), 1u);

  auto wide = CoverageDB::ToleranceRange(100.0, 1.0, /*is_percent=*/true);
  auto wide_ivs = CoverageDB::RealRangeIntervals(
      wide.first, wide.second, /*interval=*/1.0, /*uses_dollar=*/false);
  EXPECT_EQ(wide_ivs.size(), 2u);
  EXPECT_TRUE(wide_ivs.back().high_inclusive);
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

// §19.5.1: `[]` makes one bin per value of the range list, and `[N]` spreads
// the values over N bins, B = 3 / 2 = 1 to each but the last, which takes the
// rest. A `$` bound stands for the end of the coverpoint's values, 15 above
// and 0 below. Sampling 1, 4 and 15 hits b[1], f[0] and top of the seven bins.
TEST(CovergroupInstanceSim, ArrayAndFixedCountBinsFromDeclaration) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [3:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v {\n"
                       "      bins b[] = {[1:3]}; bins f[2] = {4, 5, 6};\n"
                       "      bins top = {[14:$]}; bins bot = {[$:0]};\n"
                       "    }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 1; c.sample();\n"
                       "    v = 4; c.sample();\n"
                       "    v = 15; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=3 t=7\n");
}

// §19.5.1: a range bin holds every value of its range, however many: 99999
// lies in [0:100000], beyond the first 65536 values, so the one bin is hit.
TEST(CovergroupInstanceSim, RangeBinHoldsEveryValueOfItsRange) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int v; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint v { bins big = {[0:100000]}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin v = 99999; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=1 t=1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.5.1: a bin's trailing iff keeps its count from incrementing at a sample
// where the guard is false, so lo stays unhit.
TEST(CovergroupInstanceSim, BinIffGuardKeepsCountFromIncrementing) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v; bit en;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins lo = {0} iff (en); bins hi = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    en = 0; v = 0; c.sample();\n"
                 "    v = 3; c.sample();\n"
                 "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.5.1: a range bin of a real coverpoint covers the real values within the
// range, so 1.5 hits [1.0:2.0].
TEST(CovergroupInstanceSim, RealCoverpointRangeBinCountsRealSample) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  real r; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint r { bins a = {[1.0:2.0]}; bins b = {[3.0:4.0]}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    r = 1.5; c.sample();\n"
          "    void'(c.get_inst_coverage(n, t));\n"
          "    $display(\"n=%0d t=%0d\", n, t);\n"
          "  end\n"
          "endmodule\n",
          f),
      "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.5.1: a bin's trailing iff keeps its count from incrementing while the
// guard is false, a transition bin's as a value bin's: the transition 1 => 2
// completes while en is 0, so t stays uncovered.
TEST(CovergroupInstanceSim, TransitionBinIffGuardSuppressesItsCount) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; bit en; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins t = (1 => 2) iff (en); bins u "
                       "= (2 => 3); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin en = 0; v = 1; c.sample(); v = 2; "
                       "c.sample(); void'(c.get_inst_coverage(n, t)); "
                       "$display(\"n=%0d t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=0 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
