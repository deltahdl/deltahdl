#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(CrossWithCovergroup, CountsSatisfyingValueTuplesOverCartesianProduct) {
  std::vector<std::vector<int64_t>> sets = {{0, 1, 2}, {10, 20}};
  auto pred = [](const std::vector<int64_t>& t) { return t[0] + t[1] < 21; };

  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples(sets, pred), 4u);
}

TEST(CrossWithCovergroup, NoValueTuplesWhenAnySetIsEmpty) {
  auto any = [](const std::vector<int64_t>&) { return true; };
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples({{1, 2}, {}}, any), 0u);
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples({}, any), 0u);
}

TEST(CrossWithCovergroup, BareCrossIdentifierSelectsAllBinTuples) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {
      {{0}, {0}}, {{0}, {1}}, {{1}, {0}}, {{1}, {1}}};
  CrossWithMatchPolicy policy;

  auto selected = CoverageDB::SelectCrossBinTuples(candidates, nullptr, policy);
  EXPECT_EQ(selected, (std::vector<size_t>{0, 1, 2, 3}));
}

TEST(CrossWithCovergroup, WithClauseDefaultsToAtLeastOne) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0}, {0}},
                                                               {{5}, {5}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>& t) { return t[0] + t[1] < 1; };
  CrossWithMatchPolicy policy;

  auto selected = CoverageDB::SelectCrossBinTuples(candidates, &pred, policy);
  EXPECT_EQ(selected, (std::vector<size_t>{0}));
}

TEST(CrossWithCovergroup, MatchesIntegerRequiresMinimumCount) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>& t) { return t[0] + t[1] < 2; };

  CrossWithMatchPolicy two;
  two.min_count = 2;
  EXPECT_EQ(CoverageDB::SelectCrossBinTuples(candidates, &pred, two),
            (std::vector<size_t>{0}));

  CrossWithMatchPolicy one;
  EXPECT_EQ(CoverageDB::SelectCrossBinTuples(candidates, &pred, one),
            (std::vector<size_t>{0, 1}));
}

TEST(CrossWithCovergroup, MatchesDollarRequiresAllValueTuples) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>& t) { return t[0] + t[1] < 2; };

  CrossWithMatchPolicy all;
  all.require_all = true;
  EXPECT_EQ(CoverageDB::SelectCrossBinTuples(candidates, &pred, all),
            (std::vector<size_t>{0}));
}

TEST(CrossWithCovergroup, ValueTupleMapsEachCrossItemToItsCoverpoint) {
  std::vector<std::vector<int64_t>> sets = {{2}, {3}, {4}};

  auto ordered = [](const std::vector<int64_t>& t) {
    return t[0] == 2 && t[1] == 3 && t[2] == 4;
  };
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples(sets, ordered), 1u);

  auto reversed = [](const std::vector<int64_t>& t) {
    return t[0] == 4 && t[1] == 3 && t[2] == 2;
  };
  EXPECT_EQ(CoverageDB::CountSatisfyingValueTuples(sets, reversed), 0u);
}

TEST(CrossWithCovergroup, MatchesCountAboveTupleCountSelectsNothing) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>&) { return true; };

  CrossWithMatchPolicy three;
  three.min_count = 3;
  EXPECT_TRUE(
      CoverageDB::SelectCrossBinTuples(candidates, &pred, three).empty());
}

TEST(CrossWithCovergroup, MatchesDollarRejectsCandidateWithNoValueTuples) {
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{1, 2}, {}}};
  std::function<bool(const std::vector<int64_t>&)> pred =
      [](const std::vector<int64_t>&) { return true; };

  CrossWithMatchPolicy all;
  all.require_all = true;
  EXPECT_TRUE(CoverageDB::SelectCrossBinTuples(candidates, &pred, all).empty());
}

TEST(CovergroupInstanceSim, CrossWithSelectsTheProductsWhoseValuesSatisfyIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] a, b; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint a; coverpoint b;\n"
                       "    X: cross a, b { bins eq = X with (a == b); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin a = 1; b = 1; c.sample(); "
                       "void'(c.X.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=13\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CrossWithOverTooManyValueTuplesIsReported) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int a, b; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint a; coverpoint b;\n"
                       "    X: cross a, b { bins eq = X with (a == b); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin c.sample(); "
                       "void'(c.X.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=4096\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross 'X': the `with` expression ranges over "
                            "more than the 1048576 value tuples deltahdl "
                            "evaluates",
                            5, "19.6.1.2"));
}

TEST(CovergroupInstanceSim, NonPositiveMatchesCountFromAFormalIsReported) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg (int m);\n"
      "    coverpoint a; coverpoint b;\n"
      "    X: cross a, b {\n"
      "      bins eq = X with (a == b) matches m;\n"
      "      bins s = '{ '{1,1}, '{2,2} } matches m;\n"
      "    }\n"
      "  endgroup\n"
      "  cg c0 = new(0);\n"
      "  cg c1 = new(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross 'X': the matches count 0 is not a positive "
                            "integer",
                            6, "19.6.1.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cross 'X': the matches count 0 is not a positive "
                            "integer",
                            7, "19.6.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

std::string TupleCounts(const std::string& design, const char* group_name) {
  SimFixture f;
  RunCapture(design, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const CoverGroup* group = f.ctx.CoverageData().FindGroup(group_name);
  if (group == nullptr || group->crosses.empty()) return "no cross";
  std::string counts;
  for (const CrossBin& bin : group->crosses[0].bins) {
    if (bin.name.rfind('<', 0) == 0) continue;
    counts += bin.name + "=" + std::to_string(bin.bin_tuples.size()) + ":" +
              std::to_string(bin.hit_count) + " ";
  }
  return counts;
}

const char* const kTwoRangePoints =
    "    ca: coverpoint a { bins lo = {[0:1]}; bins hi = {[2:3]}; }\n"
    "    cb: coverpoint b { bins lo = {[0:1]}; bins hi = {[2:3]}; }\n";

TEST(CovergroupInstanceSim, MatchesOverMultiValueBinsFromSource) {
  EXPECT_EQ(TupleCounts(std::string("module top;\n"
                                    "  bit [1:0] a, b;\n"
                                    "  covergroup cg;\n") +
                            kTwoRangePoints +
                            "    X: cross ca, cb {\n"
                            "      bins d = X with (ca <= cb);\n"
                            "      bins m3 = X with (ca <= cb) matches 3;\n"
                            "      bins m4 = X with (ca <= cb) matches 4;\n"
                            "      bins all = X with (ca <= cb) matches $;\n"
                            "    }\n"
                            "  endgroup\n"
                            "  cg c = new;\n"
                            "  initial begin a = 0; b = 3; c.sample(); end\n"
                            "endmodule\n",
                        "c"),
            "d=3:1 m3=3:1 m4=1:1 all=1:1 ");
}

TEST(CovergroupInstanceSim, ABareCrossIdentifierFromSourceSelectsEveryTuple) {
  EXPECT_EQ(TupleCounts(std::string("module top;\n"
                                    "  bit [1:0] a, b;\n"
                                    "  covergroup cg;\n") +
                            kTwoRangePoints +
                            "    X: cross ca, cb { bins all = X; }\n"
                            "  endgroup\n"
                            "  cg c = new;\n"
                            "  initial begin\n"
                            "    a = 0; b = 3; c.sample(); a = 2; c.sample();\n"
                            "  end\n"
                            "endmodule\n",
                        "c"),
            "all=4:2 ");
}

TEST(CovergroupInstanceSim, AWithReadingAFormalSelectsPerInstance) {
  const std::string kDesign = std::string(
                                  "module top;\n"
                                  "  bit [1:0] a, b;\n"
                                  "  covergroup cg (int lim);\n") +
                              kTwoRangePoints +
                              "    X: cross ca, cb { bins s = X with (ca + cb "
                              "< lim); }\n"
                              "  endgroup\n"
                              "  cg c = new(1);\n"
                              "  cg d = new(3);\n"
                              "endmodule\n";
  EXPECT_EQ(TupleCounts(kDesign, "c"), "s=1:0 ");
  EXPECT_EQ(TupleCounts(kDesign, "d"), "s=3:0 ");
}

TEST(CovergroupInstanceSim, EveryWithFormBuildsItsCrossBinFromSource) {
  EXPECT_EQ(TupleCounts(std::string("module top;\n"
                                    "  bit [1:0] a, b;\n"
                                    "  covergroup cg;\n") +
                            kTwoRangePoints +
                            "    X: cross ca, cb {\n"
                            "      bins bw = binsof(ca) with (ca > 2);\n"
                            "      bins pw = (binsof(ca) intersect {0}) with "
                            "(cb == 3);\n"
                            "      bins ow = binsof(ca.lo) with (ca == 0) ||\n"
                            "                binsof(cb.hi) with (cb == 3);\n"
                            "    }\n"
                            "  endgroup\n"
                            "  cg c = new;\n"
                            "endmodule\n",
                        "c"),
            "bw=2:0 pw=1:0 ow=3:0 ");
}

TEST(CovergroupInstanceSim, AWithReadsACrossedVariablesValue) {
  EXPECT_EQ(TupleCounts("module top;\n"
                        "  bit [1:0] a; bit b;\n"
                        "  covergroup cg;\n"
                        "    X: cross a, b { bins s = X with (a == 2 && b); }\n"
                        "  endgroup\n"
                        "  cg c = new;\n"
                        "endmodule\n",
                        "c"),
            "s=1:0 ");
}

TEST(CovergroupInstanceSim, AWithYieldingAnUnknownDoesNotSatisfy) {
  EXPECT_EQ(TupleCounts("module top;\n"
                        "  bit [1:0] a; bit b;\n"
                        "  parameter logic [1:0] M = 2'bx1;\n"
                        "  covergroup cg;\n"
                        "    X: cross a, b { bins s = X with (a & M); }\n"
                        "  endgroup\n"
                        "  cg c = new;\n"
                        "endmodule\n",
                        "c"),
            "s=4:0 ");
}

}  // namespace
