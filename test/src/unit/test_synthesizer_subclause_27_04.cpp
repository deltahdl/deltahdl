#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

namespace {

// §27.4 gives each instance of a loop generate block an implicit localparam
// named after the genvar, an integer holding that iteration's value, so a
// genvar read as an operand stands for its instance's value. Each case fails on
// a lowering that reads the genvar as constant zero.

TEST(GenvarOperandSynthesis, GenvarBitIsItsInstancesValue) {
  ExpectInputSweep(
      "module m (input [3:0] a, output logic [3:0] y);\n"
      "  for (genvar i = 0; i < 4; i++) begin : g\n"
      "    assign y[i] = a[i] & i[0];\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0xAu; });
}

// The implicit localparam is a signed integer, so beside the signed int M = -1
// the comparison `M < i` is signed (§11.4.4) and holds in every instance. It
// fails on a lowering that reads the genvar unsigned, which makes the
// comparison unsigned, where -1 is the largest value and `M < i` never holds.
TEST(GenvarOperandSynthesis, GenvarOperandIsASignedInteger) {
  ExpectInputSweep(
      "module m (input [3:0] a, output logic [3:0] y);\n"
      "  localparam int M = -1;\n"
      "  for (genvar i = 0; i < 4; i++) begin : g\n"
      "    assign y[i] = (M < i) ? a[i] : 1'b1;\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a; });
}

// §27.4 allows a localparam inside a generate block, and §23.9 makes each
// generate block a scope of its own, so a parameter read as an operand inside a
// block stands for that block's value. Each case fails on a lowering that
// reports the block's parameter as having no lowering, or reads another
// scope's parameter of the same name.

TEST(GenerateBlockParameterSynthesis, BlockLocalparamIsItsValue) {
  ExpectInputSweep(
      "module m (input [3:0] a, output logic [3:0] y);\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    localparam Q = 4'b1010;\n"
      "    assign y = a & Q;\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0xAu; });
}

TEST(GenerateBlockParameterSynthesis, BlockLocalparamShadowsModuleParameter) {
  ExpectInputSweep(
      "module m #(parameter Q = 4'b0101)\n"
      "    (input [3:0] a, output logic [3:0] y);\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    localparam Q = 4'b1010;\n"
      "    assign y = a & Q;\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0xAu; });
}

TEST(GenerateBlockParameterSynthesis, EachBlockReadsItsOwnLocalparam) {
  ExpectInputSweep(
      "module m (input [3:0] a, output logic [3:0] y);\n"
      "  if (1) begin : g1\n"
      "    localparam logic [1:0] K = 2'b01;\n"
      "    assign y[1:0] = a[1:0] & K;\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    localparam logic [1:0] K = 2'b10;\n"
      "    assign y[3:2] = a[3:2] & K;\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0x9u; });
}

}  // namespace
