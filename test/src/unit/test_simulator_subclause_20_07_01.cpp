#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ArrayQueryOverVariableDimensionsSim, CountsEveryDimensionOfAnArray) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a[3][][5];\n"
                       "  initial $display(\"%0d %0d %0d %0d\", "
                       "$unpacked_dimensions(a), $size(a, 1), $size(a, 3), "
                       "$size(a, 4));\n"
                       "endmodule\n",
                       f),
            "3 3 5 32\n");
}

TEST(ArrayQueryOverVariableDimensionsSim, CountsEachFixedDimensionPastIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int b[2][][2][3:1];\n"
                       "  initial $display(\"%0d %0d %0d %0d\", "
                       "$unpacked_dimensions(b), $size(b, 3), $size(b, 4), "
                       "$left(b, 4));\n"
                       "endmodule\n",
                       f),
            "4 2 3 3\n");
}

TEST(ArrayQueryOverVariableDimensionsSim, CountsTheDynamicDimensionsPastIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int d[2][];\n"
                       "  int e[2][][];\n"
                       "  initial $display(\"%0d %0d\", "
                       "$unpacked_dimensions(d), $unpacked_dimensions(e));\n"
                       "endmodule\n",
                       f),
            "2 3\n");
}

TEST(ArrayQueryOverVariableDimensionsSim,
     QueriesTheDynamicArrayAnElementHolds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a[3][][5];\n"
                       "  initial begin\n"
                       "    a[2] = new[4];\n"
                       "    $display(\"OUT %0d %0d\", $size(a[2], 1), "
                       "$size(a[1], 1));\n"
                       "    $display(\"OUT %0d %0d %0d\", $left(a[2]), "
                       "$right(a[2]), $increment(a[2]));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "OUT 4 0\nOUT 0 3 -1\n");
}

TEST(ArrayQueryOverVariableDimensionsSim, SizesAParameterArrayAtRunTime) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct { logic valid; bit [8:1] data; } "
                       "MyType;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"OUT %0d %0d %0d %0d\", $size(A), "
                       "$size(logic [5:0]), $left(int), $bits(MyType));\n"
                       "endmodule\n",
                       f),
            "OUT 4 6 31 9\n");
}

TEST(ArrayQueryOverVariableDimensionsSim, CountsEveryLevelOfAQueue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int qq[$][$];\n"
                       "  int dd[][];\n"
                       "  int q3[$][$][$];\n"
                       "  initial $display(\"%0d %0d %0d\", "
                       "$unpacked_dimensions(qq), $unpacked_dimensions(dd), "
                       "$unpacked_dimensions(q3));\n"
                       "endmodule\n",
                       f),
            "2 2 3\n");
}

TEST(ArrayQueryOverVariableDimensionsSim,
     BoundsTheFixedDimensionsOfAQueuesElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int q[$][2][3:1];\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", "
                       "$unpacked_dimensions(q), $size(q, 2), $size(q, 3), "
                       "$left(q, 3), $size(q, 4));\n"
                       "endmodule\n",
                       f),
            "3 2 3 3 32\n");
}

}  // namespace
