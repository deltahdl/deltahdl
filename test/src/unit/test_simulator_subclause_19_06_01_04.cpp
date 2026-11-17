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

std::string SetBinTuples(const char* group_name) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit [1:0] a, b;\n"
      "  typedef struct { bit [1:0] ca; bit [1:0] cb; } pv_t;\n"
      "  typedef pv_t pq_t[$];\n"
      "  typedef struct { bit [3:0] w; } other_t;\n"
      "  other_t oq[$] = '{ '{4'h5} };\n"
      "  covergroup cg (int lim);\n"
      "    ca: coverpoint a { bins lo = {[0:1]}; bins hi = {[2:3]}; }\n"
      "    cb: coverpoint b { bins lo = {[0:1]}; bins hi = {[2:3]}; }\n"
      "    X: cross ca, cb {\n"
      "      function CrossQueueType mk(int n);\n"
      "        for (int i = 0; i < n; i++) mk.push_back('{i, i});\n"
      "      endfunction\n"
      "      bins d = '{ '{0,0}, '{2,0} };\n"
      "      bins m2 = '{ '{0,0}, '{1,1}, '{0,2} } matches 2;\n"
      "      bins all = '{ '{0,2}, '{0,3}, '{1,2}, '{1,3}, '{2,2} } "
      "matches $;\n"
      "      bins fn = mk(lim);\n"
      "      bins cst = pq_t'(oq);\n"
      "    }\n"
      "  endgroup\n"
      "  cg c = new(1);\n"
      "  cg g = new(3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const CoverGroup* group = f.ctx.CoverageData().FindGroup(group_name);
  if (group == nullptr || group->crosses.empty()) return "no cross";
  std::string tuples;
  for (const CrossBin& bin : group->crosses[0].bins) {
    if (bin.name.rfind('<', 0) == 0) continue;
    tuples += bin.name + "=" + std::to_string(bin.bin_tuples.size()) + " ";
  }
  return tuples;
}

TEST(CovergroupInstanceSim, SetPoliciesOverMultiValueBinsFromSource) {
  EXPECT_EQ(SetBinTuples("c"), "d=2 m2=1 all=1 fn=1 cst=1 ");
}

TEST(CovergroupInstanceSim, ACrossFunctionOfAFormalGivesBinsPerInstance) {
  EXPECT_EQ(SetBinTuples("g"), "d=2 m2=1 all=1 fn=2 cst=1 ");
}

}  // namespace
