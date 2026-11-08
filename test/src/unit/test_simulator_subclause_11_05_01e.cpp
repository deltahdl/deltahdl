#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterSelectSim, OutOfRangeSelectOfAFourStateParameterReadsX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  localparam logic Q = P[9];\n"
      "  localparam logic [3:0] R = P[9:6];\n"
      "  parameter logic [127:0] W = {64'h1, 64'hFFFF_FFFF_FFFF_FFFF};\n"
      "  localparam logic [63:0] L = W[63:0];\n"
      "  initial $display(\"%b %b %h\", Q, R, L);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x xx11 ffffffffffffffff\n");
}

TEST(SelectAddressSim, IndexWiderThanSixtyFourBitsIsOutOfBounds) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v = 8'hFF;\n"
      "  logic [64:0] i = {1'b1, 64'd3};\n"
      "  logic [63:0] j = 64'h8000_0000_0000_0003;\n"
      "  logic signed [64:0] k = -65'sd1;\n"
      "  logic signed [64:0] m = {2'b01, 63'd3};\n"
      "  logic [64:0] n = 65'd3;\n"
      "  initial begin\n"
      "    $display(\"%b %b %b %b %b %b\", v[i], v[j], v[k], v[m], v[n],\n"
      "             v[i +: 2]);\n"
      "    v[i] = 1'b0;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x x x x 1 xx\nff\n");
}

}  // namespace
