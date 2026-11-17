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

std::string CleanRun(const std::string& design) {
  SimFixture f;
  std::string out = RunCapture(design, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  return out;
}

TEST(IgnoreBinsSim, IgnoredValuesLeaveTheBinsAfterTheValuesAreSplit) {
  EXPECT_EQ(CleanRun("module top;\n"
                     "  bit [2:0] v; int n, t;\n"
                     "  covergroup cg;\n"
                     "    pa: coverpoint v { bins s[2] = {[0:3]};\n"
                     "      ignore_bins ig = {0, 1}; }\n"
                     "    pb: coverpoint v { bins x = {1, 2}; bins y = {3};\n"
                     "      ignore_bins ig = {1, 2}; }\n"
                     "  endgroup\n"
                     "  cg c = new;\n"
                     "  initial begin\n"
                     "    v = 2; c.sample(); v = 3; c.sample();\n"
                     "    void'(c.pa.get_inst_coverage(n, t));\n"
                     "    $display(\"pa %0d %0d\", n, t);\n"
                     "    void'(c.pb.get_inst_coverage(n, t));\n"
                     "    $display(\"pb %0d %0d\", n, t);\n"
                     "  end\n"
                     "endmodule\n"),
            "pa 1 1\npb 1 1\n");
}

TEST(IgnoreBinsSim, AnIgnoredValueLeavesATransitionThroughIt) {
  EXPECT_EQ(CleanRun("module top;\n"
                     "  bit [2:0] v; int n, t;\n"
                     "  covergroup cg;\n"
                     "    coverpoint v { bins t = (1 => 2); bins o = {5};\n"
                     "      ignore_bins ig = {2}; }\n"
                     "  endgroup\n"
                     "  cg c = new;\n"
                     "  initial begin\n"
                     "    v = 1; c.sample(); v = 2; c.sample();\n"
                     "    void'(c.get_inst_coverage(n, t));\n"
                     "    $display(\"%0d %0d\", n, t);\n"
                     "  end\n"
                     "endmodule\n"),
            "1 2\n");
}

TEST(IgnoreBinsSim, EveryFormOfIgnoreBinRemovesItsValues) {
  EXPECT_EQ(
      CleanRun(
          "module top;\n"
          "  bit [2:0] v; int n, t;\n"
          "  int arr[2] = '{1, 5};\n"
          "  covergroup c1;\n"
          "    coverpoint v { bins b[] = {[0:7]};\n"
          "      ignore_bins ig[] = {[2:3], 6}; }\n"
          "  endgroup\n"
          "  covergroup c2;\n"
          "    coverpoint v { bins b[] = {[0:7]};\n"
          "      wildcard ignore_bins ig = {3'b1??}; }\n"
          "  endgroup\n"
          "  covergroup c3;\n"
          "    coverpoint v { bins b[] = {[0:7]};\n"
          "      ignore_bins ig = {[0:7]} with (item % 2 == 1); }\n"
          "  endgroup\n"
          "  covergroup c4;\n"
          "    coverpoint v { bins b[] = {[0:7]}; ignore_bins ig = arr; }\n"
          "  endgroup\n"
          "  covergroup c5;\n"
          "    coverpoint v { bins b[] = {[0:7]};\n"
          "      ignore_bins ig[2] = {0, 1, 2, 3}; }\n"
          "  endgroup\n"
          "  c1 g1 = new; c2 g2 = new; c3 g3 = new; c4 g4 = new;\n"
          "  c5 g5 = new;\n"
          "  initial begin\n"
          "    v = 6; g1.sample(); v = 7; g1.sample();\n"
          "    v = 5; g2.sample(); v = 3; g2.sample();\n"
          "    v = 3; g3.sample(); v = 4; g3.sample();\n"
          "    v = 5; g4.sample(); v = 4; g4.sample();\n"
          "    v = 2; g5.sample(); v = 4; g5.sample();\n"
          "    void'(g1.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, "
          "t);\n"
          "    void'(g2.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, "
          "t);\n"
          "    void'(g3.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, "
          "t);\n"
          "    void'(g4.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, "
          "t);\n"
          "    void'(g5.get_inst_coverage(n, t)); $display(\"%0d %0d\", n, "
          "t);\n"
          "  end\n"
          "endmodule\n"),
      "1 5\n1 4\n1 4\n1 6\n1 4\n");
}

TEST(IgnoreBinsSim, IgnoreBinsRemoveValuesInEveryPlace) {
  EXPECT_EQ(
      CleanRun(
          "covergroup ucg (ref bit [1:0] v);\n"
          "  coverpoint v { bins b[] = {[0:3]}; ignore_bins ig = {2}; }\n"
          "endgroup\n"
          "package pk;\n"
          "  covergroup pcg (ref bit [1:0] v);\n"
          "    coverpoint v { bins b[] = {[0:3]}; ignore_bins ig = {2}; }\n"
          "  endgroup\n"
          "endpackage\n"
          "interface ifc;\n"
          "  bit [1:0] v; int n, t;\n"
          "  covergroup icg;\n"
          "    coverpoint v { bins b[] = {[0:3]}; ignore_bins ig = {2}; }\n"
          "  endgroup\n"
          "  icg c = new;\n"
          "  initial begin\n"
          "    #1 v = 2; c.sample(); v = 3; c.sample();\n"
          "    void'(c.get_inst_coverage(n, t)); $display(\"i %0d %0d\", n, "
          "t);\n"
          "  end\n"
          "endinterface\n"
          "program pg;\n"
          "  bit [1:0] v; int n, t;\n"
          "  covergroup gcg;\n"
          "    coverpoint v { bins b[] = {[0:3]}; ignore_bins ig = {2}; }\n"
          "  endgroup\n"
          "  gcg c = new;\n"
          "  initial begin\n"
          "    #9 v = 2; c.sample(); v = 3; c.sample();\n"
          "    void'(c.get_inst_coverage(n, t)); $display(\"p %0d %0d\", n, "
          "t);\n"
          "  end\n"
          "endprogram\n"
          "module top;\n"
          "  class K;\n"
          "    bit [1:0] w;\n"
          "    covergroup kcg;\n"
          "      coverpoint w { bins b[] = {[0:3]}; ignore_bins ig = {2}; }\n"
          "    endgroup\n"
          "    function new(); kcg = new; endfunction\n"
          "  endclass\n"
          "  bit [1:0] v; int n, t;\n"
          "  ifc i();\n"
          "  pg g();\n"
          "  pk::pcg p = new(v);\n"
          "  ucg u = new(v);\n"
          "  if (1) begin : gen\n"
          "    bit [1:0] x; int gn, gt;\n"
          "    covergroup bcg;\n"
          "      bit [1:0] cx: coverpoint x { bins b[] = {[0:3]}; ignore_bins "
          "ig = {2}; }\n"
          "    endgroup\n"
          "    bcg c = new;\n"
          "    initial begin\n"
          "      #3 x = 2; c.sample(); x = 3; c.sample();\n"
          "      void'(c.get_inst_coverage(gn, gt));\n"
          "      $display(\"g %0d %0d\", gn, gt);\n"
          "    end\n"
          "  end\n"
          "  initial begin\n"
          "    automatic K k = new;\n"
          "    #4 k.w = 2; k.kcg.sample(); k.w = 3; k.kcg.sample();\n"
          "    void'(k.kcg.get_inst_coverage(n, t)); $display(\"k %0d %0d\", "
          "n, t);\n"
          "    v = 2; p.sample(); u.sample(); v = 3; p.sample(); u.sample();\n"
          "    void'(p.get_inst_coverage(n, t)); $display(\"pk %0d %0d\", n, "
          "t);\n"
          "    void'(u.get_inst_coverage(n, t)); $display(\"u %0d %0d\", n, "
          "t);\n"
          "  end\n"
          "endmodule\n"),
      "i 1 3\ng 1 3\nk 1 3\npk 1 3\nu 1 3\np 1 3\n");
}

}  // namespace
