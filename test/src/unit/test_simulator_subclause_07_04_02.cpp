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

// §7.4.2 / §11.2.1: the size of a fixed-size unpacked array may be given by a
// parameter. End-to-end, the top element is only addressable when that bound
// resolves in the parameter scope; a mis-resolved (zero) size would make this
// access fall outside the array.
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

// The three cases above declare at module scope, which the lowerer builds. A
// declaration written inside a procedural block is built by
// CreateBlockArrayElements in statement_assign_decl.cpp instead, and that read
// only §7.4.2's range form: the size form registered no array and created no
// elements, so `a[i]` was a bit-select of the single carrier variable the
// declaration left behind. Each case below is carried out through a
// module-scope scalar, because a block-local array's element variables go away
// with the block and cannot be looked up once the run has ended.

// §7.4.2: [size] is shorthand for [0:size-1], so index 2 of `int a[3]` is the
// top element and holds what was written to it. A bit-select of the carrier
// writes bit 2 instead, and 9 truncated to that one bit reads 1.
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

// §7.4.2 states the two spellings as the same array, giving `int Array[8][32]`
// and `int Array[0:7][0:31]` as one declaration written two ways, so the claim
// is an equality rather than two readings that happen to agree. The range form
// already built its array here, so the comparison reads 0 while the size form
// does not: 5 written through a bit-select comes back as 1.
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

// One element read cannot say the elements are separate storage: three bits of
// one carrier answer to three indices too. Writing all three and summing them
// separates the readings, 11 + 22 + 33 against the 1 + 0 + 1 that the low three
// bits of the carrier hold once each value has been cut down to one bit.
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

// §7.10 writes a queue's dimension as `$`, which is not a size however much it
// looks like one dimension written in one pair of brackets. CreateBlockQueue is
// asked before the array builder and answers for it; this case is what says the
// size form did not take the queue's dimension away from it, and it would read
// 0 from a queue that was never built.
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

// §7.4.2 in an instantiated module: `int a[4]` declared in M, which top
// instantiates as `m`, is stored under "m.a" and its elements under "m.a[i]",
// and §23.9 resolves the bare name `a` inside M through the instance. The
// lookup for the array's shape (SimContext::FindArrayInfo) asked for the bare
// key alone, so an element read `a[1]` found no array and fell to a bit-select
// of the carrier variable the lowerer creates under the name -- a carrier the
// element writes never touch -- reading 0 for both terms; the elements read
// back 22 and 44.
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

// §12.7.3 and §20.7 on the same array: foreach steps through the four
// elements and $size answers the declared dimension, both asking the array's
// shape by its bare name inside the instance (§23.9). With no shape found,
// foreach ran once per bit of the 32-bit carrier and $size measured that
// carrier, answering 32; the loop fills 10, 20, 30, 40 and the sum is 100
// under a size of 4.
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

// §7.4.2 (printed page 154): an element of a net array is used as a scalar or
// vector net is, so each element is driven and resolved apart from the others.
// `assign n[1] = 1'b1;` drives n[1] alone and leaves n[0] and n[2] undriven at
// z; the two drivers of the wor element r[0] are or-ed and r[1], driven by
// neither, is z; and a bit-select of an element of `wire [3:0] v[2:1]` drives
// that one bit of it. The array was held as one net of an element's width, so
// n[1] selected a bit it did not have and read x, as did every element.
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

// The same elements as the targets of output ports: each instance drives the
// one element its connection names, `.y(nouts[2])`, and an array of instances
// over the whole array drives one element per instance, left index to left
// index (§23.3.3.5). An element no instance drives stays z. A net array a child
// declares is its own per instance and reads by hierarchical name.
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

// §7.4.2 with §7.2 and §10.9.2: each element of an unpacked array of
// structures is a structure, so a nested pattern initializer packs each item
// by the element's layout -- reds 3, 1 and 2 -- and a member write to an
// element, `c[1].green = 7`, and a whole-element pattern assignment,
// `c[2] = '{9, 8, 7}`, are stored and read back through `c[i].member`.
// Packed at the items' own widths and written to no layout, every member read
// 0.
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

// §7.4.2 with §7.2: each element of a multidimensional unpacked array of
// structures is a structure too, so a member write to `c[x][y]`, by indices
// written out and by a foreach with a loop variable per dimension, is stored
// in that element and read back through `c[x][y].member`.
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

// §7.4.2 with §8.5: a class property may be a multidimensional unpacked
// array, and each element `g[i][j]` is a variable of its own, written and
// read in a method, through a handle, and by a foreach with a loop variable
// per dimension.
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

// §12.7.3 with §7.4.2 and §8.5: a foreach naming a loop variable per
// dimension of a multidimensional class property reached through a handle,
// `foreach (h.g[i, j])` in an initial block, runs as nested loops over all
// six elements, the last dimension varying fastest.
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

// §7.4.2 with §6.16: an element of a fixed-size array of strings is a string
// variable, so it holds the whole text of each write rather than as many
// characters as the first one: "longer" after "x" keeps all six, in an array
// a module declares with one dimension or two and in one a block declares.
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

// §7.4, §7.8 and §7.10 with §26.3 and §6.16: an element of a package's array
// of strings named through the package scope is a string, so a string method
// reads its text and one that writes its object writes it, for a queue, a
// fixed-size and an associative array alike.
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

}  // namespace
