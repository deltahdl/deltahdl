#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, WildcardBinMatchesValues) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "data");
  CoverBin wbin;
  wbin.name = "w_even";
  wbin.kind = CoverBinKind::kWildcard;
  wbin.values = {0, 2, 4, 6};
  CoverageDB::AddBin(cp, wbin);

  db.Sample(g, {{"data", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"data", 3}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, IgnoredValuesRemovedFromStateBin) {
  std::vector<int64_t> bin_values = {5, 7, 8, 7, 9};
  std::vector<int64_t> ignored = {7, 8};
  EXPECT_EQ(CoverageDB::RemoveIgnoredValues(bin_values, ignored),
            (std::vector<int64_t>{5, 9}));

  EXPECT_EQ(CoverageDB::RemoveIgnoredValues({1, 2, 3}, {4}),
            (std::vector<int64_t>{1, 2, 3}));
}

TEST(Coverage, IgnoredValuesRemovedAfterDistribution) {
  std::vector<int64_t> values = {1, 2, 3, 4, 5, 6};
  auto distributed = CoverageDB::DistributeValues(values, 3);
  std::vector<int64_t> ignored = {3, 4};
  std::vector<std::vector<int64_t>> remaining;
  remaining.reserve(distributed.size());
  for (const auto& bin : distributed) {
    remaining.push_back(CoverageDB::RemoveIgnoredValues(bin, ignored));
  }
  EXPECT_EQ(remaining, (std::vector<std::vector<int64_t>>{{1, 2}, {}, {5, 6}}));
}

TEST(Coverage, CoveredTransitionRemovedWhenContainsIgnored) {
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({2, 3}, {2, 3}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({2, 9, 3}, {2, 3}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3, 4}, {5, 6}));
}

TEST(Coverage, IgnoreTransitionMustBeBounded) {
  EXPECT_TRUE(CoverageDB::IgnoreTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kConsecutive)));
  EXPECT_FALSE(CoverageDB::IgnoreTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kGoto)));
  EXPECT_FALSE(CoverageDB::IgnoreTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(
          TransitionRepeatKind::kNonconsecutive)));
}

TEST(Coverage, IgnoringEveryValueEmptiesStateBin) {
  EXPECT_TRUE(CoverageDB::RemoveIgnoredValues({1, 2, 3}, {3, 1, 2}).empty());
  EXPECT_TRUE(CoverageDB::RemoveIgnoredValues({}, {5}).empty());
}

TEST(Coverage, EmptyIgnoreSetLeavesStateBinUnchanged) {
  EXPECT_EQ(CoverageDB::RemoveIgnoredValues({4, 2, 4, 6}, {}),
            (std::vector<int64_t>{4, 2, 4, 6}));
}

TEST(Coverage, LongerIgnoredSequenceDoesNotRemoveTransition) {
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({2, 3}, {1, 2, 3, 4}));
}

TEST(Coverage, EmptyIgnoredSequenceDoesNotRemoveTransition) {
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3}, {}));
}

TEST(Coverage, IgnoredSequenceMatchedAtTransitionBoundaries) {
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3}, {2, 3}));
}

TEST(Coverage, IgnoreBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin ign;
  ign.name = "ignore";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {7, 8};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, IgnoredValueRecordsNoHitAtSampleTime) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin ign;
  ign.name = "ignore";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {7};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 7}});

  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

TEST(Coverage, IgnoredStateValueDoesNotSuppressTransitionThroughIt) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");

  CoverBin trans;
  trans.name = "seq";
  trans.kind = CoverBinKind::kTransition;
  trans.transitions = {{1, 2, 3, 4}};
  CoverageDB::AddBin(cp, trans);

  CoverBin ign;
  ign.name = "ign_state";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {3};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 2}});
  db.Sample(g, {{"s", 3}});
  db.Sample(g, {{"s", 4}});

  EXPECT_EQ(cp->bins[0].hit_count, 1u);
  EXPECT_EQ(cp->bins[1].hit_count, 0u);
}

TEST(Coverage, IgnoredValueInAnotherBinIsNotCounted) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin ord;
  ord.name = "ordinary";
  ord.values = {5, 6};
  CoverageDB::AddBin(cp, ord);

  CoverBin ign;
  ign.name = "ignore";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {5};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 5}});
  EXPECT_EQ(cp->bins[0].hit_count, 0u);

  db.Sample(g, {{"x", 6}});
  EXPECT_EQ(cp->bins[0].hit_count, 1u);
}

TEST(Coverage, IgnoreTransitionBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");

  CoverBin good;
  good.name = "good_trans";
  good.kind = CoverBinKind::kTransition;
  good.transitions = {{1, 2}};
  CoverageDB::AddBin(cp, good);

  CoverBin ign;
  ign.name = "ign_trans";
  ign.kind = CoverBinKind::kIgnore;
  ign.transitions = {{7, 8}};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 2}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(CovergroupInstanceSim, IgnoreBinsFromDeclarationRemoveValues) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] v; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint v { bins v[] = {[0:3]}; ignore_bins ig = {1}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    v = 1; c.sample();\n"
          "    v = 2; c.sample();\n"
          "    void'(c.get_inst_coverage(n, t));\n"
          "    $display(\"n=%0d t=%0d\", n, t);\n"
          "  end\n"
          "endmodule\n",
          f),
      "n=1 t=3\n");
}

TEST(CovergroupInstanceSim, IgnoredTransitionLeavesTheTransitionBins) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins t[] = (1 => 2), (2 => 3); "
                       "ignore_bins ig = (2 => 3); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin v = 1; c.sample(); v = 2; c.sample(); "
                       "void'(c.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, IgnoredTransitionRemovesASequenceContainingIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [2:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins t = (1 => 2 => 3 => 4);\n"
                       "      bins u = (2 => 4); bins one = {1};\n"
                       "      ignore_bins x = (2 => 3); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 1; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
