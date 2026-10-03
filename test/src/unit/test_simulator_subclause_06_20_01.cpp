// §6.20.1 Parameter declaration syntax — a parameter declared with unpacked
// dimensions is an array of values, assigned by an assignment pattern, and
// §6.20.2 makes each element hold the value the pattern gives it, so these
// tests read the elements back out of a running module.
#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Positional items fill the elements from the left bound, so A[1] is the
// second item and A[3] the fourth. With no run-time value both read x.
TEST(ParameterArraySim, PositionalPatternFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", A[1], A[3]);\n"
                       "endmodule\n",
                       f),
            "2 4\n");
}

// §10.9.1 counts positional items from the dimension's left bound, so a
// descending [3:0] puts the first item at address 3.
TEST(ParameterArraySim, DescendingDimensionTakesItemsFromTheLeft) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam int D[3:0] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", D[3], D[0]);\n"
                       "endmodule\n",
                       f),
            "1 4\n");
}

// Two unpacked dimensions take a nested pattern, one brace per dimension.
TEST(ParameterArraySim, NestedPatternFillsTwoDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int M[2][2] = '{'{1, 2}, '{3, 4}};\n"
                       "  initial $display(\"%0d %0d\", M[0][1], M[1][0]);\n"
                       "endmodule\n",
                       f),
            "2 3\n");
}

// A default: key gives every element its value.
TEST(ParameterArraySim, DefaultKeyFillsEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int K[3] = '{default: 7};\n"
                       "  initial $display(\"%0d %0d\", K[0], K[2]);\n"
                       "endmodule\n",
                       f),
            "7 7\n");
}

// An element of a real parameter array holds a real, its fraction kept.
TEST(ParameterArraySim, RealElementsKeepTheirFractions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R[2] = '{1.5, 0.25};\n"
                       "  initial $display(\"%g %g\", R[0], R[1]);\n"
                       "endmodule\n",
                       f),
            "1.5 0.25\n");
}

// A parameter port may be declared an array as a body parameter may, and its
// elements take its pattern the same way.
TEST(ParameterArraySim, ParameterPortArrayFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter int A[2] = '{1, 2});\n"
                       "  initial $display(\"%0d %0d\", A[0], A[1]);\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

}  // namespace
