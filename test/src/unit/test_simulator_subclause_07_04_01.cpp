#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedArraySimulation, MultiDimPackedArrayAsSingleVector) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 16'hABCD;\n"
      "    result = x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABCDu);
}

TEST(PackedArraySimulation, MultiDimPackedArrayPartSelect) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    x = 16'hABCD;\n"
      "    result = x[1:1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedArraySimulation, PackedArrayBitSelect) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    x = 8'b10100101;\n"
      "    result = x[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(PackedArraySimulation, PartSelectIsUnsigned) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  logic signed [15:0] result;\n"
      "  initial begin\n"
      "    x = 8'sb10000001;\n"
      "    result = x[7:4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x0008u);
}

TEST(PackedArraySimulation, SignedPackedArrayWidensWithSignExtension) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  logic signed [15:0] result;\n"
      "  initial begin\n"
      "    x = -8'sd2;\n"
      "    result = x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFFFEu);
}

TEST(PackedArraySimulation, IntCanBeSelectedAsPackedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    x = 32'hDEADBEEF;\n"
      "    result = x[31:24];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xDEu);
}

TEST(PackedArraySimulation, ElementOfPackedArrayIsUnsigned) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  logic signed [15:0] result;\n"
      "  initial begin\n"
      "    x[1] = 8'h80;\n"
      "    x[0] = 8'h00;\n"
      "    result = x[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x0080u);
}

TEST(PackedArraySimulation, ByteCanBeSelectedAsPackedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte x;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    x = 8'hAB;\n"
      "    result = x[7:4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAu);
}

TEST(PackedArraySimulation, ElementOfSignedNamedTypeIsSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef logic signed [7:0] s8_t;\n"
      "  typedef bit signed s1_t;\n"
      "  s8_t [1:0] x;\n"
      "  s8_t [1:0][1:0] z;\n"
      "  s1_t [3:0] b;\n"
      "  s8_t [1:0] y [2];\n"
      "  logic signed [15:0] r, rz, rb, ry;\n"
      "  logic signed [31:0] ru;\n"
      "  initial begin\n"
      "    x[1] = 8'h80;\n"
      "    z[1] = 16'h8080;\n"
      "    b[1] = 1'b1;\n"
      "    y[1] = 16'h0101;\n"
      "    y[1][0] = 8'h80;\n"
      "    y[5][0] = 8'h7f;\n"
      "    r = x[1];\n"
      "    rz = z[1][0];\n"
      "    ru = z[1];\n"
      "    rb = b[1];\n"
      "    ry = y[1][0];\n"
      "    $display(\"%h %h %h %h %0d\", r, rz, ru, rb, x[1] < 0);\n"
      "    $display(\"%h %h %0d\", ry, y[1], y[1][0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ff80 ff80 00008080 ffff 1\nff80 0180 1\n");
}

TEST(PackedArraySimulation, EnumWithDimsAfterItsBodyIsAnArrayOfIt) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  enum bit [1:0] {A, B, C} [3:0] v;\n"
      "  enum {P, Q} [1:0] w;\n"
      "  struct packed { enum bit [1:0] {X, Y} [2:0] e; bit f; } r;\n"
      "  initial begin\n"
      "    v[1] = B;\n"
      "    v[2] = C;\n"
      "    w[1] = Q;\n"
      "    $display(\"%0d %h %0d %0d\", $bits(v), v, v[2], v[2] == C);\n"
      "    $display(\"%0d %0d %0d %0d\", $bits(w), w[1], w[0], $bits(r));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 24 2 1\n64 1 0 7\n");
}

TEST(PackedArraySimulation, AggregateWithDimsAfterItsBodyIsAnArrayOfIt) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } [3:0] s;\n"
      "  typedef union packed { bit [7:0] x; bit [7:0] y; } [2:0] u_t;\n"
      "  u_t u;\n"
      "  struct packed { struct packed { bit [1:0] a; } [2:0] n;\n"
      "                  union packed { bit [1:0] x; bit [1:0] y; } [1:0] m;\n"
      "                  bit f; } q;\n"
      "  initial begin\n"
      "    s = '0;\n"
      "    s[1] = 16'hABCD;\n"
      "    $display(\"%0d %h %h\", $bits(s), s, s[1]);\n"
      "    $display(\"%0d %0d\", $bits(u), $bits(q));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 00000000abcd0000 abcd\n24 11\n");
}

TEST(PackedArraySimulation, BlockEnumArrayIsIndexedByElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    typedef enum bit [1:0] {A, B, C} [1:0] e_t;\n"
      "    e_t x;\n"
      "    enum logic [2:0] {P, Q} [1:0] w;\n"
      "    enum logic [2:0] {R, S} y;\n"
      "    x[1] = C;\n"
      "    x[0] = B;\n"
      "    w[1] = Q;\n"
      "    w[0] = P;\n"
      "    y = S;\n"
      "    $display(\"%b %b %b %b %b\", x, x[1], w, w[1], y[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1001 10 001000 001 1\n");
}

TEST(PackedArraySimulation, PackedVectorFormalTakesEveryBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic int h(logic [1:0][3:0] x);\n"
                       "    return x + $bits(x) * 1000;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d\", h(8'h06));\n"
                       "endmodule\n",
                       f),
            "8006\n");
}

TEST(PackedArraySimulation,
     DISABLED_PackedArrayOfTypedefInputFormalTakesEveryBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef logic [3:0] nib_t;\n"
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "package pk;\n"
          "  function automatic int f(nib_t [1:0] x); return x + $bits(x) * "
          "1000; endfunction\n"
          "  function automatic int g(ps_t [1:0] x); return x[1].lo + $bits(x) "
          "* 1000; endfunction\n"
          "endpackage\n"
          "class K;\n"
          "  static function int f(nib_t [1:0] x); return x + $bits(x) * 1000; "
          "endfunction\n"
          "  static function int g(ps_t [1:0] x); return x[1].lo + $bits(x) * "
          "1000; endfunction\n"
          "endclass\n"
          "module t;\n"
          "  function automatic int f(nib_t [1:0] x); return x + $bits(x) * "
          "1000; endfunction\n"
          "  function automatic int g(ps_t [1:0] x); return x[1].lo + $bits(x) "
          "* 1000; endfunction\n"
          "  initial begin\n"
          "    $display(\"%0d %0d\", f(8'h06), g(16'h5A00));\n"
          "    $display(\"%0d %0d\", pk::f(8'h06), pk::g(16'h5A00));\n"
          "    $display(\"%0d %0d\", K::f(8'h06), K::g(16'h5A00));\n"
          "  end\n"
          "endmodule\n",
          f),
      "8006 16010\n"
      "8006 16010\n"
      "8006 16010\n");
}

TEST(PackedArraySimulation,
     DISABLED_PackedArrayOfTypedefOutputAndInoutFormalsTakeEveryBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef logic [3:0] nib_t;\n"
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "module t;\n"
          "  function automatic void o(output nib_t [1:0] x); x = 8'h96; "
          "endfunction\n"
          "  function automatic void io(inout nib_t [1:0] x); x = x + 1; "
          "endfunction\n"
          "  task automatic tk(input nib_t [1:0] x, output int r); r = x + "
          "$bits(x) * 1000; endtask\n"
          "  task automatic to(output ps_t [1:0] x); x = 16'hA5C3; endtask\n"
          "  logic [7:0] b;\n"
          "  logic [15:0] w;\n"
          "  int r;\n"
          "  initial begin\n"
          "    o(b);\n"
          "    $display(\"%h\", b);\n"
          "    b = 8'h7f;\n"
          "    io(b);\n"
          "    $display(\"%h\", b);\n"
          "    tk(8'h06, r);\n"
          "    $display(\"%0d\", r);\n"
          "    to(w);\n"
          "    $display(\"%h\", w);\n"
          "  end\n"
          "endmodule\n",
          f),
      "96\n"
      "80\n"
      "8006\n"
      "a5c3\n");
}

TEST(PackedArraySimulation,
     DISABLED_PackedArrayOfTypeParameterOrTypedefPropertyTakesEveryBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
          "class C #(type T = logic [7:0], type P = ps_t);\n"
          "  typedef logic [7:0] bt;\n"
          "  T [3:0] a;\n"
          "  static T [1:0] s;\n"
          "  bt [3:0] b;\n"
          "  static bt [1:0] sb;\n"
          "  P [1:0] p;\n"
          "  function void t();\n"
          "    a = '1; s = '1; b = '1; sb = '1; p = 16'h5A00;\n"
          "    $display(\"%0d %0d %0d %0d %0d %h %h %0d\", $bits(a), $bits(s), "
          "$bits(b),\n"
          "             $bits(sb), $bits(p), a, s, p[1].lo);\n"
          "  endfunction\n"
          "endclass\n"
          "module m;\n"
          "  C c;\n"
          "  C #(logic [15:0]) d;\n"
          "  initial begin\n"
          "    c = new;\n"
          "    c.t();\n"
          "    d = new;\n"
          "    d.t();\n"
          "  end\n"
          "endmodule\n",
          f),
      "32 16 32 16 16 ffffffff ffff 10\n"
      "64 32 32 16 16 ffffffffffffffff ffffffff 10\n");
}

TEST(PackedArraySimulation, PackedArrayOfTypeParameterInAModuleTakesEveryBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m #(type T = logic [7:0], parameter int Q [2] = '{0, 2});\n"
          "  T [3:0] a;\n"
          "  T [Q[1]:0] w;\n"
          "  initial begin\n"
          "    a = '1;\n"
          "    w = '1;\n"
          "    $display(\"%0d %h %0d %h\", $bits(a), a, $bits(w), w);\n"
          "  end\n"
          "endmodule\n",
          f),
      "32 ffffffff 24 ffffff\n");
}

}  // namespace
