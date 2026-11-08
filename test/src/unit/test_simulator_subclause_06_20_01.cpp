#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterArraySim, PositionalPatternFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", A[1], A[3]);\n"
                       "endmodule\n",
                       f),
            "2 4\n");
}

TEST(ParameterArraySim, DescendingDimensionTakesItemsFromTheLeft) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam int D[3:0] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", D[3], D[0]);\n"
                       "endmodule\n",
                       f),
            "1 4\n");
}

TEST(ParameterArraySim, NestedPatternFillsTwoDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int M[2][2] = '{'{1, 2}, '{3, 4}};\n"
                       "  initial $display(\"%0d %0d\", M[0][1], M[1][0]);\n"
                       "endmodule\n",
                       f),
            "2 3\n");
}

TEST(ParameterArraySim, DefaultKeyFillsEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int K[3] = '{default: 7};\n"
                       "  initial $display(\"%0d %0d\", K[0], K[2]);\n"
                       "endmodule\n",
                       f),
            "7 7\n");
}

TEST(ParameterArraySim, RealElementsKeepTheirFractions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R[2] = '{1.5, 0.25};\n"
                       "  initial $display(\"%g %g\", R[0], R[1]);\n"
                       "endmodule\n",
                       f),
            "1.5 0.25\n");
}

TEST(ParameterArraySim, ParameterPortArrayFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter int A[2] = '{1, 2});\n"
                       "  initial $display(\"%0d %0d\", A[0], A[1]);\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

}  // namespace
