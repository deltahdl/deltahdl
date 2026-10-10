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
      "  logic signed [15:0] r, rz, rb;\n"
      "  logic signed [31:0] ru;\n"
      "  initial begin\n"
      "    x[1] = 8'h80;\n"
      "    z[1] = 16'h8080;\n"
      "    b[1] = 1'b1;\n"
      "    r = x[1];\n"
      "    rz = z[1][0];\n"
      "    ru = z[1];\n"
      "    rb = b[1];\n"
      "    $display(\"%h %h %h %h %0d\", r, rz, ru, rb, x[1] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ff80 ff80 00008080 ffff 1\n");
}

}  // namespace
