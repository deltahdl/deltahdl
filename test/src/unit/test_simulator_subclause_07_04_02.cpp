#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(UnpackedArraySimulation, ElementWriteAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = arr[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAAu);
}

TEST(UnpackedArraySimulation, RangeFormElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[2] = 8'h42;\n"
      "    result = mem[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x42u);
}

TEST(UnpackedArraySimulation, ParameterSizedArrayElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int N = 4;\n"
      "  logic [7:0] arr [N];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[3] = 8'h55;\n"
      "    result = arr[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x55u);
}

TEST(UnpackedArraySimulation, SizeFormInAProceduralBlockAddressesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    a[0] = 7;\n"
      "    a[2] = 9;\n"
      "    result = a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(UnpackedArraySimulation, SizeFormAndRangeFormAgreeInAProceduralBlock) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    int b[0:2];\n"
      "    a[2] = 5;\n"
      "    b[2] = 5;\n"
      "    result = (a[2] == b[2]);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(UnpackedArraySimulation, SizeFormInAProceduralBlockGivesEachIndexItsOwn) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    a[0] = 11;\n"
      "    a[1] = 22;\n"
      "    a[2] = 33;\n"
      "    result = a[0] + a[1] + a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 66u);
}

TEST(UnpackedArraySimulation, QueueDimensionInAProceduralBlockIsNotASize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int q[$];\n"
      "    q.push_back(7);\n"
      "    result = q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(UnpackedArraySimulation, ChildInstanceElementsReadBackByBareName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int a[4];\n"
      "  int r;\n"
      "  initial begin\n"
      "    a[0] = 11;\n"
      "    a[1] = 22;\n"
      "    a[2] = 33;\n"
      "    a[3] = 44;\n"
      "    r = a[1] * 100 + a[3];\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 2244u);
}

TEST(UnpackedArraySimulation, ChildInstanceForeachAndSizeSeeTheArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int a[4];\n"
      "  int r, s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    foreach (a[i]) a[i] = (i + 1) * 10;\n"
      "    foreach (a[i]) s = s + a[i];\n"
      "    r = $size(a) * 1000 + s;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 4100u);
}

TEST(UnpackedArraySimulation, NetArrayElementsAreNetsOfTheirOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire n[0:2];\n"
                       "  wor r[2];\n"
                       "  wire [3:0] v[2:1];\n"
                       "  assign n[1] = 1'b1;\n"
                       "  assign r[0] = 1'b0;\n"
                       "  assign r[0] = 1'b1;\n"
                       "  assign v[2] = 4'hA;\n"
                       "  assign v[1][0] = 1'b1;\n"
                       "  initial #1 $display(\"%b%b%b %b%b %b %b\", n[0], "
                       "n[1], n[2], r[0], r[1], v[2], v[1]);\n"
                       "endmodule\n",
                       f),
            "z1z 1z 1010 zzz1\n");
}

TEST(UnpackedArraySimulation, MultidimensionalNetArrayElementsAreNets) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire n[0:2][4:5];\n"
                       "  assign n[1][5] = 1'b1;\n"
                       "  initial #1 $display(\"%b%b%b\", n[1][5], n[1][4], "
                       "n[2][5]);\n"
                       "endmodule\n",
                       f),
            "1zz\n");
}

TEST(UnpackedArraySimulation, NetArrayElementsDrivenThroughOutputPorts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input logic a, output wire y);\n"
                       "  assign y = ~a;\n"
                       "endmodule\n"
                       "module sub;\n"
                       "  wire [3:0] w[0:1];\n"
                       "  assign w[1] = 4'h5;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire nouts[3:0];\n"
                       "  wire o[3];\n"
                       "  logic ins[0:2] = '{1'b1, 1'b0, 1'b1};\n"
                       "  leaf w(.a(1'b1), .y(nouts[2]));\n"
                       "  leaf x(.a(1'b0), .y(nouts[0]));\n"
                       "  leaf u[2:0](.a(ins), .y(o));\n"
                       "  sub s();\n"
                       "  initial #1 $display(\"%b%b%b%b %b%b%b %h %h\", "
                       "nouts[3], nouts[2], nouts[1], nouts[0], o[0], o[1], "
                       "o[2], s.w[1], s.w[0]);\n"
                       "endmodule\n",
                       f),
            "z0z1 010 5 z\n");
}

TEST(UnpackedArraySim, StructElementsInitializedWrittenAndRead) {
  const char* src =
      "module t;\n"
      "  typedef struct { byte red, green, blue; } c_t;\n"
      "  c_t c[3] = '{'{3, 0, 0}, '{1, 0, 0}, '{2, 0, 0}};\n"
      "  int reds, g1, b2, sum;\n"
      "  initial begin\n"
      "    reds = c[0].red * 100 + c[1].red * 10 + c[2].red;\n"
      "    c[1].green = 7;\n"
      "    c[2] = '{9, 8, 7};\n"
      "    g1 = c[1].green;\n"
      "    b2 = c[2].blue;\n"
      "    sum = 0;\n"
      "    foreach (c[i]) sum += c[i].red;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "reds"), 312u);
  EXPECT_EQ(RunAndGet(src, "g1"), 7u);
  EXPECT_EQ(RunAndGet(src, "b2"), 7u);
  EXPECT_EQ(RunAndGet(src, "sum"), 13u);
}

TEST(UnpackedArraySim, MultidimensionalStructElementsWrittenAndRead) {
  const char* src =
      "module t;\n"
      "  typedef struct { int i; int j; } p_t;\n"
      "  p_t c [11:12][6:8];\n"
      "  int direct, sum;\n"
      "  initial begin\n"
      "    c[12][7].j = 5;\n"
      "    direct = c[12][7].j;\n"
      "    foreach (c[x, y]) begin\n"
      "      c[x][y].i = x - 10;\n"
      "      c[x][y].j = y - 5;\n"
      "    end\n"
      "    sum = 0;\n"
      "    foreach (c[x, y]) sum += c[x][y].i * c[x][y].j;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "direct"), 5u);
  EXPECT_EQ(RunAndGet(src, "sum"), 18u);
}

TEST(UnpackedArraySim, MultidimensionalClassPropertyElementsAreVariables) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int g[2][3];\n"
      "    function void set(); g[1][2] = 5; g[0][1] = 3; endfunction\n"
      "    function int get(); return g[1][2] * 10 + g[0][1]; endfunction\n"
      "    function int total();\n"
      "      int s = 0;\n"
      "      foreach (g[i, j]) s += g[i][j];\n"
      "      return s;\n"
      "    endfunction\n"
      "    function void fill(); foreach (g[i, j]) g[i][j] = i * 3 + j; "
      "endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new; h.set();\n"
      "    h.g[1][0] = 7;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", h.get(), h.g[1][2], h.g[0][1],\n"
      "             h.g[1][0], h.total());\n"
      "    h.fill();\n"
      "    $display(\"%0d %0d %0d\", h.g[0][2], h.g[1][1], h.total());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "53 5 3 7 15\n2 4 15\n");
}

TEST(UnpackedArraySim, ForeachOverAMultidimensionalPropertyThroughAHandle) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int g[2][3];\n"
      "  endclass\n"
      "  C h;\n"
      "  int s, n, last;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    foreach (h.g[i, j]) begin h.g[i][j] = i * 3 + j; n++; last = j; "
      "end\n"
      "    foreach (h.g[i, j]) s += h.g[i][j];\n"
      "    $display(\"%0d %0d %0d %0d\", n, s, h.g[1][2], last);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6 15 5 2\n");
}

TEST(UnpackedArraySim, AStringElementHoldsTheWholeTextOfEachWrite) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string sh[2];\n"
      "  string m[2][2];\n"
      "  initial begin\n"
      "    string b[2][2];\n"
      "    sh[0] = \"x\"; sh[0] = \"longer\";\n"
      "    m[1][0] = \"x\"; m[1][0] = \"longer\";\n"
      "    b[0][1] = \"x\"; b[0][1] = \"longer\";\n"
      "    sh[1] = \"cdef\"; sh[1] = \"g\";\n"
      "    $display(\"%s %s %s %s %0d\", sh[0], m[1][0], b[0][1], sh[1],\n"
      "             sh[1].len());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "longer longer longer g 1\n");
}

TEST(UnpackedArraySim, AStringMethodActsOnAPackageScopedElement) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  string pq[$];\n"
      "  string pf[2];\n"
      "  string ps[int];\n"
      "endpackage\n"
      "module t;\n"
      "  initial begin\n"
      "    p::pq.push_back(\"ab\"); p::pf[1] = \"abc\"; p::ps[0] = \"abcd\";\n"
      "    $display(\"%0d %0d %0d\", p::pq[0].len(), p::pf[1].len(),\n"
      "             p::ps[0].len());\n"
      "    p::pq[0].putc(0, \"Q\"); p::pf[1].putc(0, \"Q\");\n"
      "    p::ps[0].putc(0, \"Q\");\n"
      "    $display(\"%s %s %s\", p::pq[0], p::pf[1], p::ps[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 3 4\nQb Qbc Qbcd\n");
}

TEST(UnpackedArraySim, ANegativeBoundInAProceduralBlockIsSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    int b [-2:1];\n"
      "    b[-2] = 7; b[1] = 9;\n"
      "    $display(\"%0d %0d %0d\", b[-2], b[1], $size(b));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 9 4\n");
}

}  // namespace
