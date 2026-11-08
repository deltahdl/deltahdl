#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(CrossSetExpressionSelect, ArrayLiteralQueueSelectsMatchingBinTuples) {
  std::vector<std::vector<int64_t>> queue = {{1, 2}, {3, 4}, {5, 6}};
  std::vector<std::vector<std::vector<int64_t>>> candidates = {
      {{1}, {2}}, {{1}, {4}}, {{3}, {4}}, {{5}, {6}}};
  CrossWithMatchPolicy policy;

  auto selected = CoverageDB::SelectCrossBinTuplesBySetExpression(
      candidates, queue, policy);
  EXPECT_EQ(selected, (std::vector<size_t>{0, 2, 3}));
}

TEST(CrossSetExpressionSelect, DefaultPolicySelectsOnAnyPresentValueTuple) {
  std::vector<std::vector<int64_t>> queue = {{2, 7}};
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{1, 2}, {7}}};
  CrossWithMatchPolicy policy;

  EXPECT_EQ(CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue,
                                                            policy),
            (std::vector<size_t>{0}));
}

TEST(CrossSetExpressionSelect, BinTupleAbsentFromQueueIsNotSelected) {
  std::vector<std::vector<int64_t>> queue = {{1, 2}, {3, 4}};
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{9}, {9}}};
  CrossWithMatchPolicy policy;

  EXPECT_TRUE(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, policy)
          .empty());
}

TEST(CrossSetExpressionSelect, MatchesIntegerRequiresMinimumPresentCount) {
  std::vector<std::vector<int64_t>> queue = {{0, 0}, {1, 0}};
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};

  CrossWithMatchPolicy two;
  two.min_count = 2;
  EXPECT_EQ(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, two),
      (std::vector<size_t>{0}));

  CrossWithMatchPolicy one;
  EXPECT_EQ(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, one),
      (std::vector<size_t>{0, 1}));
}

TEST(CrossSetExpressionSelect, MatchesDollarRequiresAllValueTuplesPresent) {
  std::vector<std::vector<int64_t>> queue = {{0, 0}, {1, 0}};
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{0, 1}, {0}},
                                                               {{0, 5}, {0}}};

  CrossWithMatchPolicy all;
  all.require_all = true;
  EXPECT_EQ(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, all),
      (std::vector<size_t>{0}));
}

TEST(CrossSetExpressionSelect, EmptyQueueSelectsNothing) {
  std::vector<std::vector<int64_t>> queue;
  std::vector<std::vector<std::vector<int64_t>>> candidates = {{{1}, {2}},
                                                               {{3}, {4}}};
  CrossWithMatchPolicy policy;

  EXPECT_TRUE(
      CoverageDB::SelectCrossBinTuplesBySetExpression(candidates, queue, policy)
          .empty());
}

TEST(CovergroupInstanceSim,
     CrossSetExpressionSelectsTheProductsHoldingItsTuples) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] a, b; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint a; coverpoint b;\n"
                       "    X: cross a, b { bins one = '{ '{1,2}, '{3,0} }; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin a = 1; b = 2; c.sample(); "
                       "void'(c.X.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=15\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim,
     CrossSetFunctionSelectsTheProductsHoldingTheTuplesItReturns) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] a, b; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint a; coverpoint b;\n"
                       "    X: cross a, b {\n"
                       "      function CrossQueueType mysel();\n"
                       "        mysel.push_back('{1,2});\n"
                       "        mysel.push_back('{3,0});\n"
                       "      endfunction\n"
                       "      bins one = mysel();\n"
                       "    }\n"
                       "  endgroup\n"
                       "  cg d = new;\n"
                       "  cg c = new;\n"
                       "  initial begin a = 1; b = 2; c.sample(); "
                       "void'(c.X.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=15\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim,
     CrossSetQueueAndSliceSelectTheProductsHoldingTuples) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] a, b; int n, t, m, u;\n"
                       "  typedef struct { bit [1:0] a; bit [1:0] b; } vt;\n"
                       "  vt q[$] = '{ '{1,2}, '{3,0} };\n"
                       "  covergroup cg;\n"
                       "    coverpoint a; coverpoint b;\n"
                       "    X: cross a, b { bins one = q; }\n"
                       "    Y: cross a, b { bins one = q[0:$]; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin a = 1; b = 2; c.sample(); "
                       "void'(c.X.get_inst_coverage(n, t)); "
                       "void'(c.Y.get_inst_coverage(m, u)); $display(\"%0d %0d "
                       "%0d %0d\", n, t, m, u); end\n"
                       "endmodule\n",
                       f),
            "1 15 1 15\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
