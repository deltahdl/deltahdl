#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(CoverageSetExpression, EvaluatedOnceAtConstruction) {
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(0), 1u);
}

TEST(CoverageSetExpression, NotReevaluatedPerSample) {
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(1), 1u);
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(100), 1u);
}

TEST(CovergroupInstanceSim, SetExpressionBinsTakeArrayElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [2:0] v; int n, t;\n"
                       "  int vals[] = '{1, 3, 5};\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins s[] = vals; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 3; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, SetExpressionBinsTakeQueueElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [2:0] v; int n, t;\n"
                       "  int q[$] = '{1, 3, 5};\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins s[] = q; }\n"
                       "  endgroup\n"
                       "  cg c;\n"
                       "  initial begin\n"
                       "    q.push_back(6);\n"
                       "    c = new;\n"
                       "    v = 6; c.sample();\n"
                       "    v = 3; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
