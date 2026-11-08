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

}  // namespace
