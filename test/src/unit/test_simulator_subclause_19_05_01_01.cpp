#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

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

TEST(CoverageWith, PreservesOrderAndDuplicates) {
  std::vector<int64_t> candidates = {7, 4, 4, 1, 8, 4};

  auto selected = CoverageDB::ApplyWithExpression(
      candidates, [](int64_t item) { return item % 2 == 0; });

  std::vector<int64_t> expected = {4, 4, 8, 4};
  EXPECT_EQ(selected, expected);
}

TEST(CoverageWith, RejectedOnRealCoverpoint) {
  CoverPoint integral_cp;
  integral_cp.is_real = false;
  EXPECT_TRUE(CoverageDB::WithExpressionAllowed(&integral_cp));

  CoverPoint real_cp;
  real_cp.is_real = true;
  EXPECT_FALSE(CoverageDB::WithExpressionAllowed(&real_cp));
}

TEST(CoverageWith, RangeReferenceMustNameOwnCoverpoint) {
  EXPECT_TRUE(CoverageDB::WithRangeReferenceAllowed("a", "a"));
  EXPECT_FALSE(CoverageDB::WithRangeReferenceAllowed("a", "b"));
}

TEST(CoverageWith, DistributeFirstChangesOrdering) {
  std::vector<int64_t> candidates = {0, 1, 2, 3, 4, 5, 6, 7};
  auto small = [](int64_t item) { return item < 3; };

  auto filter_first =
      CoverageDB::ApplyWithAndDistribute(candidates, small, 2, false);
  ASSERT_EQ(filter_first.size(), 2u);
  EXPECT_EQ(filter_first[0], (std::vector<int64_t>{0}));
  EXPECT_EQ(filter_first[1], (std::vector<int64_t>{1, 2}));

  auto distribute_first =
      CoverageDB::ApplyWithAndDistribute(candidates, small, 2, true);
  ASSERT_EQ(distribute_first.size(), 2u);
  EXPECT_EQ(distribute_first[0], (std::vector<int64_t>{0, 1, 2}));
  EXPECT_TRUE(distribute_first[1].empty());

  EXPECT_NE(filter_first, distribute_first);
}

TEST(CoverageWith, EmptyWhenNoCandidateMatches) {
  std::vector<int64_t> candidates = {1, 3, 5, 7};
  auto selected = CoverageDB::ApplyWithExpression(
      candidates, [](int64_t item) { return item % 2 == 0; });
  EXPECT_TRUE(selected.empty());
}

TEST(CoverageWith, DistributeIntoZeroBins) {
  std::vector<int64_t> candidates = {0, 1, 2, 3};
  auto bins = CoverageDB::ApplyWithAndDistribute(
      candidates, [](int64_t) { return true; }, 0, false);
  EXPECT_TRUE(bins.empty());
}

TEST(CovergroupInstanceSim, WithFilterKeepsMatchingValues) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [2:0] v; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint v { bins m[] = {[0:7]} with (item % 2 == 0); }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    v = 2; c.sample();\n"
          "    void'(c.get_inst_coverage(n, t));\n"
          "    $display(\"n=%0d t=%0d\", n, t);\n"
          "  end\n"
          "endmodule\n",
          f),
      "n=1 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

std::string Tally(const std::string& src) {
  SimFixture f;
  const std::string kOut = RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  return kOut;
}

std::string OnePoint(const std::string& decls, const std::string& point,
                     const std::string& samples) {
  return Tally(
      "module top;\n"
      "  int n, t;\n" +
      decls +
      "  covergroup cg;\n"
      "    " +
      point +
      "\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n" +
      samples +
      "    void'(c.get_inst_coverage(n, t));\n"
      "    $display(\"%0d %0d\", n, t);\n"
      "  end\n"
      "endmodule\n");
}

TEST(BinWithSim, EachInstanceEvaluatesTheWithClauseWithItsOwnFormal) {
  EXPECT_EQ(Tally("module top;\n"
                  "  bit [1:0] v; int n, t1, t2;\n"
                  "  covergroup cg (int lo);\n"
                  "    coverpoint v { bins b[] = {[0:3]} with (item > lo); }\n"
                  "  endgroup\n"
                  "  cg c1 = new(1);\n"
                  "  cg c2 = new(2);\n"
                  "  initial begin\n"
                  "    void'(c1.get_inst_coverage(n, t1));\n"
                  "    void'(c2.get_inst_coverage(n, t2));\n"
                  "    $display(\"%0d %0d\", t1, t2);\n"
                  "  end\n"
                  "endmodule\n"),
            "2 1\n");
}

TEST(BinWithSim, ItemTakesASignedCoverpointsType) {
  EXPECT_EQ(OnePoint("  byte v;\n",
                     "coverpoint v { bins m[] = {[-4:3]} with (item < 0); }",
                     "    v = -2; c.sample(); v = 2; c.sample();\n"),
            "1 4\n");
}

TEST(BinWithSim, DISABLED_AFunctionOfItemFiltersAsTheInlineTestDoes) {
  EXPECT_EQ(OnePoint("  bit [3:0] v;\n"
                     "  function automatic bit even(int x); return x % 2 == 0; "
                     "endfunction\n",
                     "coverpoint v { bins m[] = {[0:15]} with (even(item)); }",
                     "    v = 3; c.sample(); v = 4; c.sample();\n"),
            "1 8\n");
}

TEST(BinWithSim, TheOwnCoverpointNameStandsForEveryValue) {
  EXPECT_EQ(OnePoint("  bit [3:0] b;\n",
                     "coverpoint b { bins b[] = b with (item % 2 == 0); }",
                     "    b = 3; c.sample(); b = 4; c.sample();\n"),
            "1 8\n");
}

TEST(BinWithSim, DistributeFirstFiltersAfterTheValuesAreSplit) {
  EXPECT_EQ(
      OnePoint("  bit [2:0] v;\n",
               "type_option.distribute_first = 1;\n"
               "    coverpoint v { bins b[2] = {[0:7]} with (item < 3); }",
               "    v = 1; c.sample();\n"),
      "1 1\n");
  EXPECT_EQ(OnePoint("  bit [2:0] v;\n",
                     "coverpoint v { bins b[2] = {[0:7]} with (item < 3); }",
                     "    v = 1; c.sample();\n"),
            "1 2\n");
}

TEST(BinWithSim, TheFilterKeepsDuplicateCandidates) {
  EXPECT_EQ(
      OnePoint("  bit [3:0] v;\n",
               "coverpoint v { bins f[2] = {1, 1, 2, 2} with (item == 1); }",
               "    v = 1; c.sample();\n"),
      "2 2\n");
}

}  // namespace
