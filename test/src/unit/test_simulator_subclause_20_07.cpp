#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
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
// (127 for a byte index, byte being signed), $size is the number of elements
// currently allocated,
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
                    {"r", 127},
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

// §20.7 with §23.6: the array a query function examines may be an
// instance's array named through a hierarchical reference, whose unpacked
// dimension comes first and whose packed element dimension second, as for a
// local one; so may an instance's queue.
TEST(ArrayQuerySim, HierarchicallyNamedArrayIsQueried) {
  SimFixture f;
  std::string out = RunCapture(
      "module sub; logic [7:0] mem[2:5]; int q[$] = '{1, 2, 3}; endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  initial $display(\"%0d %0d %0d %0d %0d %0d\", $size(u.mem),\n"
      "                   $left(u.mem), $right(u.mem), $high(u.mem),\n"
      "                   $size(u.mem, 2), $size(u.q));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 2 5 5 8 3\n");
}

// §20.7 with §8.5: an unpacked array property of a class object is an array
// the query functions examine -- through a handle, `logic [7:0] data[1:3]`
// with 3 elements from left 1 to right 3 and an 8-bit second dimension, a
// dynamic `int d[]` holding the count its new[] gave it, and, bare inside a
// method, the descending `bit [3:0] dn[5:2]` from left 5 to right 2.
TEST(ArrayQuerySim, ClassArrayPropertyIsQueried) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    logic [7:0] data[1:3];\n"
      "    bit [3:0] dn[5:2];\n"
      "    int d[];\n"
      "    function void show;\n"
      "      $display(\"%0d %0d %0d\", $left(dn), $right(dn),\n"
      "               $increment(dn));\n"
      "    endfunction\n"
      "  endclass\n"
      "  C m = new;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d %0d\", $size(m.data), $left(m.data),\n"
      "             $right(m.data), $size(m.data, 2));\n"
      "    m.d = new[5];\n"
      "    $display(\"%0d %0d\", $size(m.d), $right(m.d));\n"
      "    m.show();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 3 8\n5 4\n5 2 1\n");
}

// §20.7 with §7.10 and §8.5: a queue property is an array whose size is its
// element count -- two after two pushes -- and not the 32 bits of its int
// element, whether named bare in a method or through a handle.
TEST(ArrayQuerySim, QueuePropertySizeIsItsElementCount) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int q[$];\n"
      "    function void fill; q.push_back(1); q.push_back(2); endfunction\n"
      "    function void show; $display(\"%0d %0d\", $size(q), $high(q));\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new; h.fill(); h.show();\n"
      "    h.q.push_back(3);\n"
      "    $display(\"%0d %0d\", $size(h.q), $unpacked_dimensions(h.q));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1\n3 1\n");
}

// §20.7 with §7.4.2 and §8.5: a property declared with two unpacked
// dimensions, `bit [1:0] m[3][5]`, has both, 3 elements in the first and 5 in
// the second, ahead of its 2-bit packed one.
TEST(ArrayQuerySim, TwoDimensionalPropertyHasBothUnpackedDimensions) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    bit [1:0] m[3][5];\n"
      "    function void show;\n"
      "      $display(\"%0d %0d\", $unpacked_dimensions(m), $size(m, 2));\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new; h.show();\n"
      "    $display(\"%0d %0d %0d %0d\", $unpacked_dimensions(h.m),\n"
      "             $size(h.m, 1), $size(h.m, 2), $size(h.m, 3));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 5\n2 3 5 2\n");
}

// §20.7 with §7.4.2 and §8.25: an unpacked dimension sized by a value
// parameter, `int g[N]`, holds as many elements as the specialization binds
// N -- 3 by default, 6 in `Box #(string, 6)` -- and each is an element of
// its own.
TEST(ArrayQuerySim, ParameterSizedPropertyFollowsTheSpecialization) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Box #(type T = int, int N = 3);\n"
      "    T f[N];\n"
      "    int g[N];\n"
      "    function int size_f; return $size(f); endfunction\n"
      "  endclass\n"
      "  Box #(string, 6) bs;\n"
      "  Box b0;\n"
      "  initial begin\n"
      "    bs = new; b0 = new;\n"
      "    b0.g[2] = 11; b0.g[1] = 4;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", bs.size_f(), $size(bs.g),\n"
      "             $size(b0.g), b0.g[2], b0.g[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6 6 3 11 4\n");
}

// §20.7 with §7.4.2 and §8.5: an unpacked dimension naming a parameter of
// the module the class is declared in, `int fk[K]` or `int fp[P * 2]`, holds
// as many elements as the parameter gives it, each an element of its own.
TEST(ArrayQuerySim, ModuleParameterSizedPropertyIsAnArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t #(parameter int P = 3);\n"
      "  localparam int K = 4;\n"
      "  class C;\n"
      "    int fk[K];\n"
      "    int fp[P * 2];\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fk[3] = 9; h.fk[2] = 5;\n"
      "    $display(\"%0d %0d %0d %0d\", $size(h.fk), h.fk[3], h.fk[2],\n"
      "             $size(h.fp));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 9 5 6\n");
}

// §20.7 with §7.2 and §7.4.2: an unpacked array member of a structure is an
// array the query functions read by its own dimension -- `m0 [7:0]` of eight
// elements from left 7, `v [2:5]` to right 5 with its int's 32-bit second
// dimension -- in a variable, bare in a method and through a handle.
TEST(ArrayQuerySim, StructArrayMemberIsQueried) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { logic [3:0] m0 [7:0]; int v [2:5]; } s_t;\n"
      "  class C;\n"
      "    s_t r;\n"
      "    function int q(); return $size(r.v); endfunction\n"
      "  endclass\n"
      "  s_t p;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", $size(p.m0), $left(p.m0),\n"
      "             $right(p.v), $size(p.v, 2), h.q(), $size(h.r.m0));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 7 5 32 4 8\n");
}

// §20.7: the query functions return an integer, which is signed -- the -1
// of $increment for the ascending `[1:10]` prints as -1 under %0d and is
// less than 0, and so is the $right of an empty dynamic array.
TEST(ArrayQuerySim, QueryResultIsASignedInteger) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] joe [1:10];\n"
      "  int d[];\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %0d %0d\", $increment(joe), $increment(joe) < "
      "0,\n"
      "             $right(d), $increment(joe, 2));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-1 1 -1 1\n");
}

// §20.7: an array query function on a data type is legal in a constant
// expression, so a parameter, a localparam and a packed dimension fold its
// answer: a ranged vector type, an integer type's [31:0], a type of two packed
// dimensions, a typedef of sixteen bits and a packed structure of nine.
TEST(ArrayQuerySim, AQueryOnADataTypeFoldsInAConstantExpression) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef logic [16:1] Word;\n"
                 "  typedef struct packed { logic v; bit [8:1] d; } P;\n"
                 "  parameter int W = $size(logic [5:0]);\n"
                 "  localparam int L = $left(int);\n"
                 "  localparam int D = $dimensions(logic [3:0][1:0]);\n"
                 "  localparam int I = $increment(Word);\n"
                 "  localparam int S = $size(P);\n"
                 "  localparam int R = $right(logic [3:0][1:0], 2);\n"
                 "  bit [$size(Word)-1:0] v;\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d\", W, L, "
                 "D, I, S, R, $bits(v));\n"
                 "endmodule\n",
                 f),
      "6 31 2 1 9 0 16\n");
}

// §20.7: the dimensions of a parameter array are fixed, so a query of them
// folds in a constant expression, the declared [4] being [0:3] and the
// written [7:4] its own bounds.
TEST(ArrayQuerySim, AQueryOnAParameterArrayFoldsInAConstantExpression) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  parameter int B[7:4] = '{1, 2, 3, 4};\n"
                       "  localparam int N = $size(A);\n"
                       "  localparam int H = $high(A) - $low(A);\n"
                       "  localparam int U = $unpacked_dimensions(B);\n"
                       "  localparam int BL = $left(B);\n"
                       "  initial $display(\"%0d %0d %0d %0d\", N, H, U, BL);\n"
                       "endmodule\n",
                       f),
            "4 3 1 7\n");
}

// §20.7: so are the fixed unpacked dimensions of a variable, here in the
// parameter override of an instance.
TEST(ArrayQuerySim, AQueryOnAFixedVariableFoldsInAParameterOverride) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub #(int W = 1, int H = 1);\n"
                       "  initial $display(\"%0d %0d\", W, H);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic [4:0] vec[0:2];\n"
                       "  int m[2][5];\n"
                       "  sub #($size(vec) * 2, $size(m, 2)) u();\n"
                       "endmodule\n",
                       f),
            "6 5\n");
}

// §20.7: each built-in type folds with the dimension it implies -- a vector
// type's one bit and an integer type's [n-1:0] -- a ranged vector keeps the
// bounds and direction it is written with, and a typedef answers for the type
// it names: two packed dimensions, a typedef of a typedef, a packed union.
TEST(ArrayQuerySim, EachDataTypeFoldsWithTheDimensionsItHolds) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef logic [16:1] Word;\n"
                 "  typedef Word Word2;\n"
                 "  typedef logic [3:0][1:0] Two;\n"
                 "  typedef union packed { logic [3:0] a; bit [3:0] b; } U;\n"
                 "  localparam int A = $size(logic) * 1000 + $left(byte) * 10 "
                 "+ $left(shortint);\n"
                 "  localparam int B = $left(longint) * 100 + $left(time);\n"
                 "  localparam int C = $size(reg [3:0]) * 100 + $right(logic "
                 "[0:3]) * 10 + $high(logic [0:3]);\n"
                 "  localparam int D = $increment(logic [0:3]) * 10 + "
                 "$low(logic [0:3]);\n"
                 "  localparam int E = $dimensions(Two) * 100 + $size(Two, 2) "
                 "* 10 + $size(U);\n"
                 "  localparam int G = $size(Word2);\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d\", A, B, C, D, "
                 "E, G);\n"
                 "endmodule\n",
                 f),
      "1085 6363 433 -10 224 16\n");
}

// §20.7: a parameter folds with its unpacked dimensions and then the packed
// ones of its type -- an int's [31:0], a declared [7:4] -- or, declared with
// no type, the [31:0] of the integer value it holds. A real parameter has no
// dimensions, so $size of it is 'x, read as 0, and $dimensions 0.
TEST(ArrayQuerySim, AParameterFoldsWithTheDimensionsOfItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int P = 3;\n"
                       "  parameter logic [7:4] Q = 0;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  parameter U = 5;\n"
                       "  parameter real R = 1.5;\n"
                       "  localparam int S = $size(P);\n"
                       "  localparam int L = $left(Q);\n"
                       "  localparam int D = $dimensions(A);\n"
                       "  localparam int W = $size(U);\n"
                       "  localparam int RS = $size(R);\n"
                       "  localparam int RD = $dimensions(R);\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d\", S, L, "
                       "D, W, RS, RD);\n"
                       "endmodule\n",
                       f),
            "32 7 2 32 0 0\n");
}

// §20.7: a single packed dimension is queried as declared, ascending or
// descending, of a vector and of the elements of an unpacked array.
TEST(ArrayQuerySim, ASinglePackedDimensionIsQueriedAsDeclared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [0:3] u;\n"
                       "  logic [7:4] w;\n"
                       "  bit [1:4] N [3:1];\n"
                       "  initial $display(\"%0d:%0d %0d:%0d %0d %0d:%0d\", "
                       "$left(u), $right(u), $left(w), $right(w), "
                       "$increment(u), $left(N, 2), $right(N, 2));\n"
                       "endmodule\n",
                       f),
            "0:3 7:4 -1 1:4\n");
}

// §20.7: $right of an associative array dimension is the highest index value
// its index type holds, the largest positive value for a signed `int`.
TEST(ArrayQuerySim, AnAssociativeDimensionsRightIsItsIndexTypesHighest) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int aa[int];\n"
                       "  int ua[int unsigned];\n"
                       "  initial $display(\"%0d %0d\", $right(aa), "
                       "$right(ua) == 32'hffffffff);\n"
                       "endmodule\n",
                       f),
            "2147483647 1\n");
}

// §20.7: an array query on a data type at run time answers for its
// dimensions -- a typedef's as declared, two of them for a typedef of two,
// and an integer type keyword's [n-1:0] -- as a type written out does.
TEST(ArrayQuerySim, AQueryOnATypeNameAtRunTimeAnswersForItsDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef logic [16:1] Word;\n"
                       "  typedef logic [3:0][2:1] packed_reg;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", "
                       "$size(Word), $left(int), $size(packed_reg, 2), "
                       "$dimensions(packed_reg), $size(logic [5:0]));\n"
                       "endmodule\n",
                       f),
            "16 31 2 2 6\n");
}

// §20.7 with §25.9: an unpacked array member of an interface instance reached
// through a virtual interface answers for its dimensions, and $bits for its
// whole bit stream (§20.6.2).
TEST(ArrayQuerySim, AnArrayReachedThroughAVirtualInterfaceIsQueried) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface ifc;\n"
                 "  logic [7:0] mem [0:15];\n"
                 "endinterface\n"
                 "class Drv;\n"
                 "  virtual ifc vif;\n"
                 "  function void show();\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d\", $size(vif.mem), "
                 "$bits(vif.mem), $left(vif.mem, 2), $left(vif.mem), "
                 "$right(vif.mem), $dimensions(vif.mem));\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  ifc i1();\n"
                 "  Drv d = new;\n"
                 "  initial begin\n"
                 "    d.vif = i1;\n"
                 "    d.show();\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "16 128 7 0 15 2\n");
}

}  // namespace
