#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

using namespace delta;

namespace {

// What §11.5.2 array addressing lowers to. Every case drives the module's
// inputs through the netlist and reads the output word, because a netlist whose
// every output bit is constant zero is what a missing lowering produces and
// `ASSERT_NE(aig, nullptr)` holds over it.
//
// Every array below is declared with a low address other than zero wherever the
// case is about the address. §11.5.2 rules that "the address bounds given in
// the declaration of the memory determine the effect of the address
// expression", and in an array declared `[0:N]` an address and an element
// offset are the same number, so a case on `[0:N]` passes whether the
// declaration was read or not.

// The test fails on a lowering that builds nothing for an element of an
// unpacked array, which is what the synthesizer did in both directions: a write
// was reported and withheld the netlist, and a read answered constant zero
// without a word. §11.5.2 gives the syntax as `mem_name[addr_expr]`, and the
// netlist owes the element the address names.
TEST(ArrayAddressing, ReadOfAnElementCarriesWhatWasWrittenToIt) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[2] = a;\n"
      "  assign y = mem[2];\n"
      "endmodule\n",
      256, [](uint64_t a) { return a; });
}

// The test fails on a lowering that gives the whole array one element's worth
// of storage, which the case above passes because it reads the element it
// wrote. `RtlirVariable::width` is the width of one element, so an array held
// eight bits for four elements and every address reached the same bits.
TEST(ArrayAddressing, ReadOfAnElementDoesNotCarryWhatAnotherElementHolds) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[2] = a;\n"
      "  assign y = mem[3];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

// The test fails on a lowering that takes the address for an element offset
// counted from zero, which the two cases above pass because address 2 is within
// four elements either way. §11.5.2 makes the declared bounds decide, and
// address 4 of `[1:4]` is the fourth element while offset 4 is past the end.
TEST(ArrayAddressing, ElementAddressResolvesAgainstTheDeclaredAddressRange) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [1:4];\n"
      "  assign mem[4] = a;\n"
      "  assign y = mem[4];\n"
      "endmodule\n",
      256, [](uint64_t a) { return a; });
}

// The test fails on a lowering that reads a descending declaration as naming
// different elements than an ascending one. §7.4.2 admits a first value
// "greater than, equal to, or less than the second value", and either way an
// address names the element carrying that address, so `mem[4]` and `mem[1]` of
// `[4:1]` are two elements and reading one does not answer the other.
TEST(ArrayAddressing, DescendingAddressRangeReachesTheOppositeElement) {
  ExpectInputSweep(
      "module m(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] mem [4:1];\n"
      "  assign mem[4] = a;\n"
      "  assign y = mem[1];\n"
      "endmodule\n",
      256, [](uint64_t) { return uint64_t{0}; });
}

// The test fails on a lowering that resolves only an address it can fold, which
// every case above passes because each writes its address as a literal. §11.5.2
// rules that "The addr_expr can be any integer expression", so an address
// arriving on a port is an address the subclause defines, and the netlist owes
// a choice among the elements. `addr` is the only input, so the driven word is
// the address.
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

// The test fails on a lowering that wraps an address past the end of the array
// onto an element that is in range. §11.5.2 rules that an address that "is out
// of bounds" gives the value §7.4.5 describes, and a 2-state value reads 0
// where a 4-state one reads x, which is what an AIG node can carry. Every
// element is driven here, so a wrap would answer the input word rather than
// zero.
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

// The test fails on a lowering that answers an element and stops there. §11.5.2
// rules that once the word is selected, "bit-selects and part-selects shall be
// addressed in the same manner as net and variable bit-selects and part-selects
// (see 11.5.1)", so the `[3]` is resolved against the element's own declared
// range `[8:1]` and reaches storage offset 2 of the element. No case above
// writes a select over a select.
TEST(ArrayAddressing, BitSelectOfAnElementResolvesAgainstThePackedRange) {
  ExpectInputSweep(
      "module m(input [8:1] a, output y);\n"
      "  logic [8:1] mem [1:4];\n"
      "  assign mem[2] = a;\n"
      "  assign y = mem[2][3];\n"
      "endmodule\n",
      256, [](uint64_t a) { return (a >> 2) & 1u; });
}

// The test fails on a lowering that drives every element where an address names
// one, which every case above passes because none reads an element another
// statement wrote. §11.5.2 gives one address one element, so writing `mem[2]`
// leaves `mem[3]` carrying what drove it. The writes are procedural here, which
// reaches `SynthLower::LowerAssignStmt` where the cases above reach
// `SynthLower::LowerContAssign`.
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

}  // namespace
