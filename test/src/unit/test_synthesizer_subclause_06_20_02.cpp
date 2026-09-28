#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

namespace {

// §6.20.2 reads a parameter declared with a type or a range at that width and
// signedness, whatever value it took, and reads a parameter declared with
// neither at the width and signedness of its final value. Each case fails on a
// lowering that reads a parameter operand as constant zero. The two sign
// extensions, each the right-hand side of an assignment to a wider target,
// also fail on one that reads the parameter unsigned. The select
// fails on one that numbers the parameter's bits from zero rather than by the
// range it was declared with. The packed array of two dimensions is read whole,
// at the eight bits its dimensions multiply to. The last case fails on one
// that reads the value from its low 64 bits alone.

TEST(ParameterWidthSynthesis, DeclaredSignedRangeSignExtendsTheValue) {
  ExpectInputSweep(
      "module m(output logic [7:0] y);\n"
      "  localparam logic signed [3:0] S = 4'b1000;\n"
      "  assign y = S;\n"
      "endmodule\n",
      1, [](uint64_t) -> uint64_t { return 0xF8u; });
}

TEST(ParameterWidthSynthesis, UntypedParameterTakesItsValuesSignedWidth) {
  ExpectInputSweep(
      "module m #(parameter P = 3'sb100) (output logic [7:0] y);\n"
      "  assign y = P;\n"
      "endmodule\n",
      1, [](uint64_t) -> uint64_t { return 0xFCu; });
}

TEST(ParameterWidthSynthesis, SelectIsAddressedByTheDeclaredRange) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic [3:0] y);\n"
      "  localparam logic [7:4] Q = 4'b1000;\n"
      "  assign y = a & {4{Q[7]}};\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a; });
}

TEST(ParameterWidthSynthesis, MultidimensionalPackedParameterIsItsValue) {
  ExpectInputSweep(
      "module m(input [7:0] a, output logic [7:0] y);\n"
      "  localparam logic [1:0][3:0] M = 8'hA5;\n"
      "  assign y = a & M;\n"
      "endmodule\n",
      256, [](uint64_t a) -> uint64_t { return a & 0xA5u; });
}

TEST(ParameterWidthSynthesis, BitAbove63OfAWideParameterIsItsValue) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic [3:0] y);\n"
      "  localparam logic [71:0] W = 72'h80_0000_0000_0000_0000;\n"
      "  assign y = a & {4{W[71]}};\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a; });
}

}  // namespace
