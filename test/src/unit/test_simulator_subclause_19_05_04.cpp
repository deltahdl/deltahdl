#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, TransitionBinNotMatchedByScalar) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "sig");
  CoverBin tbin;
  tbin.name = "t_01";
  tbin.kind = CoverBinKind::kTransition;
  tbin.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, tbin);

  db.Sample(g, {{"sig", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, WildcardValueExpandsToContiguousGroup) {
  auto values = CoverageDB::ExpandWildcardValue(0b1100, 0b1100, 4);
  EXPECT_EQ(values, (std::vector<int64_t>{12, 13, 14, 15}));
}

TEST(Coverage, WildcardValueFixedAndWildBitExtremes) {
  EXPECT_EQ(CoverageDB::ExpandWildcardValue(0, 0, 2),
            (std::vector<int64_t>{0, 1, 2, 3}));
  EXPECT_EQ(CoverageDB::ExpandWildcardValue(0b101, 0b111, 3),
            (std::vector<int64_t>{5}));
}

TEST(Coverage, WildcardValueIgnoresBitsInWildcardPositions) {
  EXPECT_EQ(CoverageDB::ExpandWildcardValue(0b1111, 0b1100, 4),
            (std::vector<int64_t>{12, 13, 14, 15}));
}

TEST(Coverage, WildcardValueZeroWidthYieldsNothing) {
  EXPECT_TRUE(CoverageDB::ExpandWildcardValue(0, 0, 0).empty());
}

TEST(Coverage, WildcardSingleBinCountsEveryMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "g12_15";
  bin.kind = CoverBinKind::kWildcard;
  bin.values = CoverageDB::ExpandWildcardValue(0b1100, 0b1100, 4);
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 13}});
  db.Sample(g, {{"v", 15}});
  db.Sample(g, {{"v", 11}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

TEST(Coverage, WildcardArrayBinPerValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  auto values = CoverageDB::ExpandWildcardValue(0b1100, 0b1100, 4);
  ASSERT_EQ(values.size(), 4u);
  for (int64_t val : values) {
    CoverBin bin;
    bin.name = "g12_15_array[" + std::to_string(val) + "]";
    bin.kind = CoverBinKind::kWildcard;
    bin.values = {val};
    CoverageDB::AddBin(cp, bin);
  }

  db.Sample(g, {{"v", 14}});
  for (const auto& bin : g->coverpoints[0].bins) {
    uint64_t expect = (bin.values.front() == 14) ? 1u : 0u;
    EXPECT_EQ(bin.hit_count, expect);
  }
}

TEST(Coverage, WildcardTransitionExpandsLikeRangeList) {
  auto from = CoverageDB::ExpandWildcardValue(0b00, 0b10, 2);
  auto to = CoverageDB::ExpandWildcardValue(0b10, 0b10, 2);
  EXPECT_EQ(from, (std::vector<int64_t>{0, 1}));
  EXPECT_EQ(to, (std::vector<int64_t>{2, 3}));

  auto transitions = CoverageDB::ExpandSetTransition({from, to});
  EXPECT_EQ(transitions, (std::vector<std::vector<int64_t>>{
                             {0, 2}, {0, 3}, {1, 2}, {1, 3}}));
}

TEST(Coverage, WildcardTransitionBinCounts) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");
  auto from = CoverageDB::ExpandWildcardValue(0b00, 0b10, 2);
  auto to = CoverageDB::ExpandWildcardValue(0b10, 0b10, 2);
  CoverBin bin;
  bin.name = "T0_3";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = CoverageDB::ExpandSetTransition({from, to});
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 3}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, WildcardTransitionArrayBinPerSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");
  auto from = CoverageDB::ExpandWildcardValue(0b00, 0b10, 2);
  auto to = CoverageDB::ExpandWildcardValue(0b10, 0b10, 2);
  auto transitions = CoverageDB::ExpandSetTransition({from, to});
  ASSERT_EQ(transitions.size(), 4u);
  for (const auto& seq : transitions) {
    CoverBin bin;
    bin.name = "T0_3_array";
    bin.kind = CoverBinKind::kTransition;
    bin.transitions = {seq};
    CoverageDB::AddBin(cp, bin);
  }

  db.Sample(g, {{"s", 0}});
  db.Sample(g, {{"s", 3}});
  for (const auto& bin : g->coverpoints[0].bins) {
    bool is_zero_three = bin.transitions.front() == std::vector<int64_t>{0, 3};
    EXPECT_EQ(bin.hit_count, is_zero_three ? 1u : 0u);
  }
}

TEST(Coverage, WildcardExcludesUnknownSamples) {
  EXPECT_TRUE(CoverageDB::WildcardSampleIncluded(false));
  EXPECT_FALSE(CoverageDB::WildcardSampleIncluded(true));
}

TEST(Coverage, WildcardBinsForbiddenOnRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* integral_cp = CoverageDB::AddCoverPoint(g, "i");
  auto* real_cp = CoverageDB::AddCoverPoint(g, "r");
  real_cp->is_real = true;
  EXPECT_TRUE(CoverageDB::WildcardBinsAllowed(integral_cp));
  EXPECT_FALSE(CoverageDB::WildcardBinsAllowed(real_cp));
}

TEST(CovergroupInstanceSim, WildcardBinMatchesUnknownBitsBothWays) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [2:0] v;\n"
          "  covergroup cg;\n"
          "    coverpoint v { wildcard bins w = {3'b1??}; bins z = {0}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    v = 3'b101; c.sample();\n"
          "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(Coverage, ASampleWithUnknownBitsMatchesNo2StateBin) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [1:0] v;\n"
      "  logic [1:0] w = 2'bx1;\n"
      "  event e;\n"
      "  covergroup cg @(e);\n"
      "    cp: coverpoint v { bins z = {0}; bins t = {3}; }\n"
      "    cq: coverpoint w { bins o = {1}; bins t = {3}; }\n"
      "  endgroup\n"
      "  cg g = new;\n"
      "  initial begin\n"
      "    $display(\"%b %b\", v, w);\n"
      "    #1 -> e;\n"
      "    #1 $display(\"%0.2f %0.2f\", g.cp.get_inst_coverage(), "
      "g.cq.get_inst_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx x1\n0.00 0.00\n");
}

}  // namespace
