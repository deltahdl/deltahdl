#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §20.7.1 (printed page 632): its own int a[3][][5] has three unpacked
// dimensions -- the fixed 3, the dynamic one of each element, and the fixed 5
// of each of those -- so $unpacked_dimensions answers 3, $size of the first
// and third 3 and 5, and the fourth is the int's 32 bits. The dynamic
// dimension was where the count stopped: 1, then x for dimension 3.
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

// The elements' elements may have more than one fixed dimension, each its own
// dimension of the array, as declared: [3:1] is three wide with 3 at its left.
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

// A fixed array of dynamic arrays has two unpacked dimensions, and one of
// dynamic arrays of dynamic arrays three.
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

// §20.7.1: a query on an element of the array asks of the dynamic array that
// element holds, a[2] four entries after new[4] and a[1] none, its bounds
// those of a dynamic dimension (§20.7): 0 on the left, the size less one on
// the right, an increment of -1.
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

// §20.7 with §6.20.1: a parameter declared with an unpacked dimension is an
// array, so $size of it at run time is its element count, beside queries on
// a type and on a structure's bits.
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

// §20.7 with §7.4.4: a queue of queues and a dynamic array of dynamic
// arrays have an unpacked dimension per level, two and two, and three for a
// queue of queues of queues. A queue counted one whatever its elements were.
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

// A queue whose elements are arrays of more than one fixed dimension has each
// of them as a dimension of its own, as declared: [3:1] is three wide with 3
// on its left, and the int's 32 bits come after.
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
