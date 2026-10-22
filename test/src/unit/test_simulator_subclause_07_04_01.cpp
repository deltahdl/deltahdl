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

// §7.4.5: a slice of a packed array selects contiguous elements, so `x[1:1]`
// of `logic [1:0][7:0] x` is the byte element 1, not bit 1.
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
  // When a part-select extracts the high bits of a signed packed array,
  // the result must be treated as unsigned. Widening it back to a wider
  // signed receiver must zero-extend (not sign-extend) the top bit.
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
  // A packed array declared signed shall behave as a signed vector when
  // assigned to a wider signed receiver, so the MSB sign-extends.
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
  // A predefined-width integer type (here, int with predefined width 32)
  // matches and can be selected from as if it were a packed array with a
  // single [n-1:0] dimension.
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
  // An individual element of a packed array (here, the high [7:0] slice
  // of a multi-dim packed array) is unsigned by default, so widening it
  // to a wider signed receiver must zero-extend the top bit instead of
  // sign-extending it.
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
  // Corroborates that the predefined-width-as-packed-vector rule is not
  // unique to int: a byte (predefined width 8) can also be part-selected
  // as though it were a packed [7:0] type.
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

// §7.4.1: an element of a packed array is signed when its type is a named type
// declared signed, so widening one sign-extends and it compares below zero.
// Only an element of that type is: `z[1]` of `s8_t [1:0][1:0] z` is a packed
// array of two s8_t and stays unsigned, while `z[1][0]` is an s8_t. The rule
// holds for a one-bit named type too, whose element a bit-select reads.
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

// §7.4.1 with A.2.2.1: packed dimensions written after an enumeration's body
// make a packed array of the enumeration, each element as wide as its base
// type, the 2-bit `bit [1:0]` or the 32-bit default int, and an index selects
// one element; they are not the base type's dimension, which they used to
// replace (#7312).
TEST(PackedArraySimulation, EnumWithDimsAfterItsBodyIsAnArrayOfIt) {
  SimFixture f;
  // deltahdl takes w for a scalar and reports its selects (#7609); the excuse
  // goes with the fix.
  f.has_errors.Excuse();
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

// §7.4.1: a packed structure or union with packed dimensions after its body is
// a packed array of it, as wide as its members make one element times the
// elements, written plainly, through a typedef, or as a member, and an index
// selects one whole element (#7313).
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

// §7.4.1 with §7.4.4: an enumeration with packed dimensions after its body,
// declared inside a procedural block through a typedef or inline, is a packed
// array of it, so an index selects one whole enumeration; a block's plain
// enumeration with a base range is still indexed by bit (#7318).
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

}  // namespace
