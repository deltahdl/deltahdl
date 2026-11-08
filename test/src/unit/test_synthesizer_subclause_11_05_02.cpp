#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

using namespace delta;

namespace {

TEST(ArrayAddressing, ReadOfAnElementCarriesWhatWasWrittenToIt) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[2] = a;\n"
      "  assign y = mem[2];\n"
      "endmodule\n",
      256, [](uint64_t a) { return a; });
}

TEST(ArrayAddressing, ReadOfAnElementDoesNotCarryWhatAnotherElementHolds) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[2] = a;\n"
      "  assign y = mem[3];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

TEST(ArrayAddressing, ElementAddressResolvesAgainstTheDeclaredAddressRange) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[4] = a;\n"
      "  assign y = mem[4];\n"
      "endmodule\n",
      256, [](uint64_t a) { return a; });
}

TEST(ArrayAddressing, DescendingAddressRangeReachesTheOppositeElement) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [4:1];\n"
      "  assign mem[4] = a;\n"
      "  assign y = mem[1];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

TEST(ArrayAddressing, VariableAddressSelectsAmongTheElements) {
  ExpectInputSweep(
      "module m(input [1:0] addr, output [7:0] y);\n"
      "  logic [7:0] mem [0:3];\n"
      "  assign mem[0] = 8'h11;\n"
      "  assign mem[1] = 8'h22;\n"
      "  assign mem[2] = 8'h33;\n"
      "  assign mem[3] = 8'h44;\n"
      "  assign y = mem[addr];\n"
      "endmodule\n",
      4, [](uint64_t addr) { return 0x11u + 0x11u * addr; });
}

TEST(ArrayAddressing, AddressOutOfTheDeclaredRangeReadsZero) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[1] = a;\n"
      "  assign mem[2] = a;\n"
      "  assign mem[3] = a;\n"
      "  assign mem[4] = a;\n"
      "  assign y = mem[7];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

TEST(ArrayAddressing, BitSelectOfAnElementResolvesAgainstThePackedRange) {
  ExpectInputSweep(
      "module m(input [8:1] a, output y);\n"
      "  logic [8:1] mem [1:4];\n"
      "  assign mem[2] = a;\n"
      "  assign y = mem[2][3];\n"
      "endmodule\n",
      256, [](uint64_t a) { return (a >> 2) & 1u; });
}

TEST(ArrayAddressing, WriteToOneElementLeavesTheOtherElementsAlone) {
  ExpectInputSweep(
      "module m(input [7:0] a, output logic [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  always_comb begin\n"
      "    mem[1] = 8'h11;\n"
      "    mem[2] = a;\n"
      "    mem[3] = 8'h33;\n"
      "    y = mem[3];\n"
      "  end\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0x33}; });
}

TEST(ArrayAddressing, ElementOfAnArrayPortCarriesWhatWasDrivenIntoIt) {
  ExpectInputSweep(
      "module m(input [3:0] mem [1:2], output [3:0] y);\n"
      "  assign y = mem[1];\n"
      "endmodule\n",
      256, [](uint64_t v) { return v & 0xFu; });
}

TEST(ArrayAddressing, ElementOfAnArrayPortDoesNotCarryAnotherElement) {
  ExpectInputSweep(
      "module m(input [3:0] mem [1:2], output [3:0] y);\n"
      "  assign y = mem[2];\n"
      "endmodule\n",
      256, [](uint64_t v) { return (v >> 4) & 0xFu; });
}

TEST(ArrayAddressing, ArrayPortAddressResolvesAgainstTheDeclaredAddressRange) {
  ExpectInputSweep(
      "module m(input [3:0] mem [1:2], output [3:0] y);\n"
      "  assign y = mem[3];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

TEST(ArrayAddressing, ParameterSizedArrayPortIsAddressedRatherThanBitSelected) {
  ExpectInputSweep(
      "module m #(parameter int N = 2) (input [3:0] mem [N], output [3:0] y);\n"
      "  assign y = mem[1];\n"
      "endmodule\n",
      256, [](uint64_t v) { return (v >> 4) & 0xFu; });
}

TEST(ArrayAddressing, ElementOfATwoDimensionalArrayCarriesWhatWasWrittenToIt) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:2][3:4];\n"
      "  assign mem[2][4] = a;\n"
      "  assign y = mem[2][4];\n"
      "endmodule\n",
      256, [](uint64_t a) { return a; });
}

TEST(ArrayAddressing, TwoDimensionalAddressReachesOneElementOnly) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:2][3:4];\n"
      "  assign mem[2][4] = a;\n"
      "  assign y = mem[2][3];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

TEST(ArrayAddressing, SecondDimensionAddressResolvesAgainstItsOwnBounds) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:2][3:4];\n"
      "  assign mem[1][3] = a;\n"
      "  assign y = mem[1][1];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

}  // namespace
