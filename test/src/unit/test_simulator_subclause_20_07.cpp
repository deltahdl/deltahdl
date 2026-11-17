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

constexpr uint64_t kNegOne = 0xFFFFFFFFull;

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

TEST(ArrayQuerySim, ScalarIntDimensionsIsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int x;\n"
                      "  int result;\n"
                      "  initial result = $dimensions(x);\n"
                      "endmodule\n",
                      "result"),
            1u);
}

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

TEST(ArrayQuerySim, RealDimensionsIsZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  real r;\n"
                      "  int result;\n"
                      "  initial result = $dimensions(r);\n"
                      "endmodule\n",
                      "result"),
            0u);
}

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

TEST(ArrayQuerySim, DimensionTwoSelectsPackedElement) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[0:7];\n"
                      "  int result;\n"
                      "  initial result = $size(arr, 2);\n"
                      "endmodule\n",
                      "result"),
            32u);
}

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

TEST(ArrayQuerySim, EmptyQueueRightIsMinusOne) {
  EXPECT_EQ(static_cast<int32_t>(RunAndGet("module t;\n"
                                           "  int q[$];\n"
                                           "  int result;\n"
                                           "  initial result = $right(q);\n"
                                           "endmodule\n",
                                           "result")),
            -1);
}

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

TEST(ArrayQuerySim, QueryOfDimensionlessArgIsUnknown) {
  EXPECT_TRUE(
      QueryResultIsUnknown("module t;\n"
                           "  real r;\n"
                           "  integer result;\n"
                           "  initial result = $left(r);\n"
                           "endmodule\n",
                           "result"));
}

TEST(ArrayQuerySim, OutOfRangeDimensionIsUnknown) {
  EXPECT_TRUE(
      QueryResultIsUnknown("module t;\n"
                           "  int x;\n"
                           "  integer result;\n"
                           "  initial result = $size(x, 2);\n"
                           "endmodule\n",
                           "result"));
}

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

std::string RunQuery(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(ArrayQueryValues, APackedStructAndAnEnumAreQueriedAsTheirPackedRange) {
  EXPECT_EQ(
      RunQuery("module t;\n"
               "  typedef struct packed {logic [1:0] a; logic [1:0] b;} ps_t;\n"
               "  typedef enum logic [5:2] {A, B} e_t;\n"
               "  ps_t ps;\n"
               "  e_t e;\n"
               "  initial $display(\"%0d %0d %0d %0d %0d %0d\", $left(ps), "
               "$size(ps), $dimensions(ps),\n"
               "    $left(e), $size(e), $right(e));\n"
               "endmodule\n"),
      "3 4 1 5 4 2\n");
}

TEST(ArrayQueryValues, DimensionsCountsTheDimensionsOfEveryArrayAndVectorKind) {
  EXPECT_EQ(
      RunQuery("module t;\n"
               "  typedef struct packed {logic [1:0] a;} ps_t;\n"
               "  typedef union packed {logic [1:0] a; bit [1:0] b;} pu_t;\n"
               "  typedef enum {A, B} e_t;\n"
               "  bit [3:0] d[];\n"
               "  byte aa[int];\n"
               "  ps_t ps;\n"
               "  pu_t pu;\n"
               "  e_t e;\n"
               "  initial $display(\"%0d %0d %0d %0d %0d\", $dimensions(d), "
               "$dimensions(aa),\n"
               "    $dimensions(ps), $dimensions(pu), $dimensions(e));\n"
               "endmodule\n"),
      "2 2 1 1 1\n");
}

TEST(ArrayQueryValues, DISABLED_DimensionsIsZeroForEveryNonVectorType) {
  EXPECT_EQ(RunQuery("class C; endclass\n"
                     "module t;\n"
                     "  typedef struct {int a;} us_t;\n"
                     "  shortreal sr;\n"
                     "  realtime rt;\n"
                     "  us_t us;\n"
                     "  C h;\n"
                     "  event ev;\n"
                     "  chandle ch;\n"
                     "  initial $display(\"%0d %0d %0d %0d %0d %0d\", "
                     "$dimensions(sr), $dimensions(rt),\n"
                     "    $dimensions(us), $dimensions(h), $dimensions(ev), "
                     "$dimensions(ch));\n"
                     "endmodule\n"),
            "0 0 0 0 0 0\n");
}

TEST(ArrayQueryValues,
     UnpackedDimensionsCountsAnAssociativeArrayAndNothingElse) {
  EXPECT_EQ(RunQuery("class C; endclass\n"
                     "module t;\n"
                     "  typedef struct {int a;} us_t;\n"
                     "  int as[string];\n"
                     "  int ai[int];\n"
                     "  real r;\n"
                     "  us_t us;\n"
                     "  C h;\n"
                     "  initial $display(\"%0d %0d %0d %0d %0d\", "
                     "$unpacked_dimensions(as),\n"
                     "    $unpacked_dimensions(ai), $unpacked_dimensions(r), "
                     "$unpacked_dimensions(us),\n"
                     "    $unpacked_dimensions(h));\n"
                     "endmodule\n"),
            "1 1 0 0 0\n");
}

TEST(ArrayQueryValues,
     DISABLED_APerDimensionQueryOfADimensionlessOperandIsUnknown) {
  EXPECT_EQ(RunQuery("class C; endclass\n"
                     "module t;\n"
                     "  typedef struct {int a;} us_t;\n"
                     "  us_t us;\n"
                     "  C h;\n"
                     "  event ev;\n"
                     "  chandle ch;\n"
                     "  initial $display(\"%0d %0d %0d %0d\", $size(us), "
                     "$left(h), $high(ev), $low(ch));\n"
                     "endmodule\n"),
            "x x x x\n");
}

TEST(ArrayQueryValues, ADimensionOutOfRangeAtRunTimeIsUnknown) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int a[2][3];\n"
                     "  int z = 0, n = -1, p = 4, k = 2;\n"
                     "  initial $display(\"%0d %0d %0d %0d\", $size(a, z), "
                     "$left(a, n), $right(a, p),\n"
                     "    $size(a, k));\n"
                     "endmodule\n"),
            "x x x 3\n");
}

TEST(ArrayQueryValues,
     DISABLED_AnOutOfRangeOrDimensionlessQueryInAConstantIsUnknown) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int a[2][3];\n"
                     "  localparam integer M = $size(a, 5);\n"
                     "  localparam integer R = $size(real);\n"
                     "  initial $display(\"%0d %0d\", M, R);\n"
                     "endmodule\n"),
            "x x\n");
}

TEST(ArrayQueryValues, DISABLED_ATypeOperatorOverAVariableIsQueriedForItsType) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int fa[4];\n"
                     "  initial $display(\"%0d %0d\", $size(type(fa)), "
                     "$dimensions(type(fa)));\n"
                     "endmodule\n"),
            "4 2\n");
}

TEST(ArrayQueryValues,
     DISABLED_AnElementSelectThatIsAnArrayIsQueriedForTheElement) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int m[2][3];\n"
                     "  int m3[2][3][4];\n"
                     "  logic [3:0] u[2][5];\n"
                     "  int r[2][4:1];\n"
                     "  int i = 1;\n"
                     "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d\", "
                     "$size(m[0]), $size(m3[1][0]),\n"
                     "    $size(u[1]), $size(u[1], 2), $left(r[0]), "
                     "$increment(r[0]), $size(m[i]));\n"
                     "endmodule\n"),
            "3 4 5 4 4 1 3\n");
}

TEST(ArrayQueryValues,
     DISABLED_AnElementSelectThatIsAnAssociativeArrayIsQueriedForTheElement) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int as[3][string];\n"
                     "  int ai[3][int];\n"
                     "  initial begin\n"
                     "    $display(\"%0d %0d %0d\", $size(as[0]), $low(ai[0]), "
                     "$high(ai[0]));\n"
                     "    as[0][\"k\"] = 1;\n"
                     "    ai[0][7] = 1;\n"
                     "    $display(\"%0d %0d %0d\", $size(as[0]), $low(ai[0]), "
                     "$high(ai[0]));\n"
                     "  end\n"
                     "endmodule\n"),
            "0 x x\n1 7 7\n");
}

TEST(ArrayQueryValues, AnElementSelectThatIsADynamicArrayOrQueueStaysCorrect) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int d[3][];\n"
                     "  int q[3][$];\n"
                     "  initial begin\n"
                     "    d[0] = new[4];\n"
                     "    q[0].push_back(1);\n"
                     "    q[0].push_back(2);\n"
                     "    $display(\"%0d %0d\", $size(d[0]), $size(q[0]));\n"
                     "  end\n"
                     "endmodule\n"),
            "4 2\n");
}

TEST(ArrayQueryValues, ADynamicArrayAndQueueGiveTheirLowAndHighBounds) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int d[];\n"
                     "  int e[];\n"
                     "  int q[$];\n"
                     "  initial begin\n"
                     "    d = new[3];\n"
                     "    $display(\"%0d %0d %0d %0d %0d %0d\", $low(d), "
                     "$high(d), $low(e), $high(e),\n"
                     "      $low(q), $high(q));\n"
                     "  end\n"
                     "endmodule\n"),
            "0 2 0 -1 0 -1\n");
}

TEST(ArrayQueryValues,
     AnAssociativeDimensionsRightIsTheHighestValueOfEveryIndexType) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  typedef struct packed {bit a; bit b;} ix_t;\n"
                     "  int a4[bit [3:0]];\n"
                     "  int as[shortint unsigned];\n"
                     "  int ap[ix_t];\n"
                     "  int ae[int];\n"
                     "  initial $display(\"%0d %0d %0d %0d\", $right(a4), "
                     "$right(as), $right(ap),\n"
                     "    $size(ae));\n"
                     "endmodule\n"),
            "15 65535 3 0\n");
}

TEST(ArrayQueryValues, IntegerIsQueriedAsAPackedThirtyTwoBitDimension) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  integer v;\n"
                     "  initial $display(\"%0d %0d %0d %0d\", $left(integer), "
                     "$left(v), $right(v),\n"
                     "    $dimensions(v));\n"
                     "endmodule\n"),
            "31 31 0 1\n");
}

TEST(ArrayQueryValues, DISABLED_TheResultIsThirtyTwoBitsWide) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int fa[4];\n"
                     "  localparam int W = $bits($size(fa));\n"
                     "  initial $display(\"%0d %0d\", $bits($size(fa)), W);\n"
                     "endmodule\n"),
            "32 32\n");
}

TEST(ArrayQueryValues, ADimensionAtRunTimeMayBeAVariable) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  int a[3][5];\n"
                     "  int k = 2;\n"
                     "  initial $display(\"%0d\", $size(a, k));\n"
                     "endmodule\n"),
            "5\n");
}

TEST(ArrayQueryValues, DimensionsAreNumberedThroughATypedefAsIfWrittenOut) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  typedef bit [3:0][1:0] packed_reg;\n"
                     "  packed_reg n[1:5][2:8];\n"
                     "  logic [3:0][1:0] w[1:5][2:8];\n"
                     "  initial begin\n"
                     "    $display(\"%0d %0d %0d %0d\", $size(n, 1), $size(n, "
                     "2), $size(n, 3),\n"
                     "      $size(n, 4));\n"
                     "    $display(\"%0d %0d %0d %0d\", $size(w, 1), $size(w, "
                     "2), $size(w, 3),\n"
                     "      $size(w, 4));\n"
                     "  end\n"
                     "endmodule\n"),
            "5 7 4 2\n5 7 4 2\n");
}

TEST(ArrayQueryValues, TheStandardsWordAndRamExampleGivesSixteen) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  typedef logic [16:1] Word;\n"
                     "  Word Ram[0:9];\n"
                     "  initial $display(\"%0d %0d %0d\", $size(Word), "
                     "$size(Ram, 2), $size(Ram, 1));\n"
                     "endmodule\n"),
            "16 16 10\n");
}

TEST(ArrayQueryValues,
     AStringIndexedArrayAndAWildcardOrStructIndexAreAccepted) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  typedef struct packed {bit [1:0] a;} ix_t;\n"
                     "  int as[string];\n"
                     "  int aw[*];\n"
                     "  int ap[ix_t];\n"
                     "  initial begin\n"
                     "    aw[5] = 1;\n"
                     "    ap[2'd2] = 1;\n"
                     "    $display(\"%0d %0d %0d %0d %0d\", "
                     "$unpacked_dimensions(as), $size(aw),\n"
                     "      $low(aw), $left(aw), $size(ap));\n"
                     "  end\n"
                     "endmodule\n"),
            "1 1 5 0 1\n");
}

TEST(ArrayQueryValues, AVariableDeclaredWithAQueueTypedefIsQueried) {
  EXPECT_EQ(RunQuery("module t;\n"
                     "  typedef int qt[$];\n"
                     "  qt q;\n"
                     "  initial $display(\"%0d\", $size(q));\n"
                     "endmodule\n"),
            "0\n");
}

}  // namespace
