#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

// §19.5.1.2: the set_covergroup_expression is evaluated when the covergroup
// instance is constructed, so it is evaluated exactly once.
TEST(CoverageSetExpression, EvaluatedOnceAtConstruction) {
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(0), 1u);
}

// §19.5.1.2: evaluation happens at construction, not at each sampling point, so
// the count stays one no matter how many times the instance is sampled.
TEST(CoverageSetExpression, NotReevaluatedPerSample) {
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(1), 1u);
  EXPECT_EQ(CoverageDB::SetExpressionEvaluationCount(100), 1u);
}

// §19.5.1.2: a bin's values may come from an array, read at instantiation;
// one bin per element of the dynamic array vals.
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

}  // namespace
