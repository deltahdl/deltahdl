#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

namespace {

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
