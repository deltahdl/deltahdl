#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.7 array query functions report information about the dimensions of an
// actual data object, so their results depend on how that object is declared
// (packed vector, fixed unpacked array, queue, dynamic array, associative
// array, string, or real). Every test therefore drives real source through the
// full elaborate/lower/run pipeline and reads the assigned result rather than
// hand-registering an array in the simulator context.

// -1 as it lands in a 32-bit integer result (what $increment/$right report for
// a dynamically sized or empty dimension).
constexpr uint64_t kNegOne = 0xFFFFFFFFull;

// Elaborate/lower/run `src` and report whether `var` ended up all-x. Used for
// the §20.7 cases that return 'x (a dimensionless first argument, an
// out-of-range dimension index, or an empty associative array's $low/$high).
bool QueryResultIsUnknown(const std::string& src, const char* var) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable(var);
  EXPECT_NE(v, nullptr);
  return v && !v->value.IsKnown();
}

// §20.7: an integral type with a predefined width is treated as a packed array
// with a single [n-1:0] dimension. For that packed dimension $left is the
// most-significant index and $right the least, so $increment is 1 and
// $low/$high mirror $right/$left. $dimensions is 1 (a simple bit vector) and
// there are no unpacked dimensions.
TEST(ArrayQuerySim, PackedVectorBounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  int l, r, inc, lo, hi, sz, dims, udims;\n"
      "  initial begin\n"
      "    l = $left(v); r = $right(v); inc = $increment(v);\n"
      "    lo = $low(v); hi = $high(v); sz = $size(v);\n"
      "    dims = $dimensions(v); udims = $unpacked_dimensions(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"l", 31},
                    {"r", 0},
                    {"inc", 1},
                    {"lo", 0},
                    {"hi", 31},
                    {"sz", 32},
                    {"dims", 1},
                    {"udims", 0}});
}

// §20.7: $increment returns 1 when $left is greater than or *equal to* $right.
// A single-bit packed vector has $left == $right (both 0), exercising the
// equality boundary of that rule; $size is then 1.
TEST(ArrayQuerySim, SingleBitPackedIncrementBoundary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic b;\n"
      "  int l, r, inc, sz;\n"
      "  initial begin\n"
      "    l = $left(b); r = $right(b); inc = $increment(b); sz = $size(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"l", 0}, {"r", 0}, {"inc", 1}, {"sz", 1}});
}

// §20.7: $dimensions returns 1 for a nonarray type that is equivalent to a
// simple bit vector; a plain int scalar is such a type.
TEST(ArrayQuerySim, ScalarIntDimensionsIsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int x;\n"
                      "  int result;\n"
                      "  initial result = $dimensions(x);\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §20.7: a string is a nonarray type equivalent to a simple bit vector, so
// $dimensions is 1 and $unpacked_dimensions is 0, independent of the string's
// current contents.
TEST(ArrayQuerySim, StringDimensions) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "  int dims, udims;\n"
      "  initial begin\n"
      "    dims = $dimensions(s); udims = $unpacked_dimensions(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"dims", 1}, {"udims", 0}});
}

// §20.7: $dimensions returns 0 for a type that is neither an array nor
// equivalent to a simple bit vector, such as a real.
TEST(ArrayQuerySim, RealDimensionsIsZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  real r;\n"
                      "  int result;\n"
                      "  initial result = $dimensions(r);\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §20.7: for a fixed-size unpacked dimension declared in ascending order
// ([0:7]), $left is the left bound and $right the right bound. Because
// $left < $right, $increment is -1 and $low/$high mirror $left/$right. The
// array contributes one unpacked dimension plus the packed element dimension,
// so $dimensions is 2 and $unpacked_dimensions is 1.
TEST(ArrayQuerySim, FixedUnpackedAscendingBounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[0:7];\n"
      "  int l, r, inc, lo, hi, sz, dims, udims;\n"
      "  initial begin\n"
      "    l = $left(arr); r = $right(arr); inc = $increment(arr);\n"
      "    lo = $low(arr); hi = $high(arr); sz = $size(arr);\n"
      "    dims = $dimensions(arr); udims = $unpacked_dimensions(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"l", 0},
                    {"r", 7},
                    {"inc", kNegOne},
                    {"lo", 0},
                    {"hi", 7},
                    {"sz", 8},
                    {"dims", 2},
                    {"udims", 1}});
}

// §20.7: for a fixed-size dimension declared in descending order ([7:0]), $left
// is the larger bound and $right the smaller, so $increment is 1. $low/$high
// still report the numerically smallest/largest indices.
TEST(ArrayQuerySim, FixedUnpackedDescendingBounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[7:0];\n"
      "  int l, r, inc, lo, hi, sz;\n"
      "  initial begin\n"
      "    l = $left(arr); r = $right(arr); inc = $increment(arr);\n"
      "    lo = $low(arr); hi = $high(arr); sz = $size(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"l", 7}, {"r", 0}, {"inc", 1}, {"lo", 0}, {"hi", 7}, {"sz", 8}});
}

// §20.7: an array's dimensions are numbered slowest-varying first. For a
// two-dimensional unpacked array of an integral element, dimension 1 is the
// outermost unpacked extent, dimension 2 the inner unpacked extent, and
// dimension 3 the packed element. $dimensions counts all three (packed and
// unpacked); $unpacked_dimensions counts the two unpacked extents; and $size of
// each dimension reports that dimension's extent.
TEST(ArrayQuerySim, MultiDimensionalUnpackedArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[4][8];\n"
      "  int dims, udims, s1, s2, s3, l2, r2, inc2;\n"
      "  initial begin\n"
      "    dims = $dimensions(arr); udims = $unpacked_dimensions(arr);\n"
      "    s1 = $size(arr, 1); s2 = $size(arr, 2); s3 = $size(arr, 3);\n"
      "    l2 = $left(arr, 2); r2 = $right(arr, 2); inc2 = $increment(arr, "
      "2);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"dims", 3},
                    {"udims", 2},
                    {"s1", 4},
                    {"s2", 8},
                    {"s3", 32},
                    {"l2", 0},
                    {"r2", 7},
                    {"inc2", kNegOne}});
}

// §20.7: dimension 1 is the slowest varying (the unpacked array dimension); the
// packed element dimension is dimension 2. Selecting dimension 2 queries the
// 32-bit packed element width.
TEST(ArrayQuerySim, DimensionTwoSelectsPackedElement) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[0:7];\n"
                      "  int result;\n"
                      "  initial result = $size(arr, 2);\n"
                      "endmodule\n",
                      "result"),
            32u);
}

// §20.7: the optional dimension expression defaults to 1, so a query with no
// second argument reports the same slowest-varying dimension as an explicit 1.
TEST(ArrayQuerySim, DefaultDimensionIsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[0:7];\n"
      "  int without_dim, with_dim1;\n"
      "  initial begin\n"
      "    without_dim = $size(arr);\n"
      "    with_dim1 = $size(arr, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"without_dim", 8}, {"with_dim1", 8}});
}

// §20.7: the dimension expression is a constant expression (§11.2.1), so it may
// be named by a localparam rather than a literal. Selecting dimension 2 through
// a localparam still queries the packed element width.
TEST(ArrayQuerySim, DimensionExprFromLocalparam) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  localparam int D = 2;\n"
                      "  int arr[0:7];\n"
                      "  int result;\n"
                      "  initial result = $size(arr, D);\n"
                      "endmodule\n",
                      "result"),
            32u);
}

// §20.7: the dimension expression is a constant expression (§11.2.1), so it may
// equally be named by a module parameter. A parameter resolves through a
// different constant path than a localparam or a literal, so selecting
// dimension 2 through a parameter is a distinct input form of the same rule.
TEST(ArrayQuerySim, DimensionExprFromParameter) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter int D = 2;\n"
                      "  int arr[0:7];\n"
                      "  int result;\n"
                      "  initial result = $size(arr, D);\n"
                      "endmodule\n",
                      "result"),
            32u);
}

// §20.7: for a queue dimension $left is 0, $increment is -1, and $right/$size
// reflect the current element count. $low/$high mirror $left/$right under the
// -1 increment. The queue adds one unpacked dimension over the packed element.
TEST(ArrayQuerySim, QueueBounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int l, r, inc, lo, hi, sz, dims, udims;\n"
      "  initial begin\n"
      "    l = $left(q); r = $right(q); inc = $increment(q);\n"
      "    lo = $low(q); hi = $high(q); sz = $size(q);\n"
      "    dims = $dimensions(q); udims = $unpacked_dimensions(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"l", 0},
                    {"r", 2},
                    {"inc", kNegOne},
                    {"lo", 0},
                    {"hi", 2},
                    {"sz", 3},
                    {"dims", 2},
                    {"udims", 1}});
}

// §20.7: for a queue or dynamic array dimension whose current size is zero,
// $right returns -1.
TEST(ArrayQuerySim, EmptyQueueRightIsMinusOne) {
  EXPECT_EQ(static_cast<int32_t>(RunAndGet("module t;\n"
                                           "  int q[$];\n"
                                           "  int result;\n"
                                           "  initial result = $right(q);\n"
                                           "endmodule\n",
                                           "result")),
            -1);
}

// §20.7: a dynamic array dimension behaves like a queue dimension. After
// new[5], $left is 0, $right is 4, $increment is -1, and $size is 5.
TEST(ArrayQuerySim, DynamicArrayBounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  int l, r, inc, sz;\n"
      "  initial begin\n"
      "    d = new[5];\n"
      "    l = $left(d); r = $right(d); inc = $increment(d); sz = $size(d);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"l", 0}, {"r", 4}, {"inc", kNegOne}, {"sz", 5}});
}

// §20.7: on an associative array with an integral index type, $left is 0,
// $increment is -1, $right is the highest possible index value for that type
// (255 for a byte index), $size is the number of elements currently allocated,
// and $low/$high are the lowest/largest currently allocated index values.
TEST(ArrayQuerySim, AssocIntegralIndexBounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[byte];\n"
      "  int l, r, inc, lo, hi, sz;\n"
      "  initial begin\n"
      "    a[3] = 30;\n"
      "    a[9] = 90;\n"
      "    l = $left(a); r = $right(a); inc = $increment(a);\n"
      "    lo = $low(a); hi = $high(a); sz = $size(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"l", 0},
                    {"r", 255},
                    {"inc", kNegOne},
                    {"lo", 3},
                    {"hi", 9},
                    {"sz", 2}});
}

// §20.7: $low/$high of an associative array with no elements currently
// allocated return 'x (there is no lowest/largest allocated index to report).
TEST(ArrayQuerySim, EmptyAssocLowIsUnknown) {
  EXPECT_TRUE(
      QueryResultIsUnknown("module t;\n"
                           "  int a[int];\n"
                           "  integer result;\n"
                           "  initial result = $low(a);\n"
                           "endmodule\n",
                           "result"));
}

TEST(ArrayQuerySim, EmptyAssocHighIsUnknown) {
  EXPECT_TRUE(
      QueryResultIsUnknown("module t;\n"
                           "  int a[int];\n"
                           "  integer result;\n"
                           "  initial result = $high(a);\n"
                           "endmodule\n",
                           "result"));
}

// §20.7: when the first argument would make $dimensions return 0, every
// per-dimension query function returns 'x. A real has no dimensions.
TEST(ArrayQuerySim, QueryOfDimensionlessArgIsUnknown) {
  EXPECT_TRUE(
      QueryResultIsUnknown("module t;\n"
                           "  real r;\n"
                           "  integer result;\n"
                           "  initial result = $left(r);\n"
                           "endmodule\n",
                           "result"));
}

// §20.7: an out-of-range dimension index yields 'x. A scalar int has a single
// dimension, so requesting dimension 2 is out of range.
TEST(ArrayQuerySim, OutOfRangeDimensionIsUnknown) {
  EXPECT_TRUE(
      QueryResultIsUnknown("module t;\n"
                           "  int x;\n"
                           "  integer result;\n"
                           "  initial result = $size(x, 2);\n"
                           "endmodule\n",
                           "result"));
}

}  // namespace
