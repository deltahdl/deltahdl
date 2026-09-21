#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.7.1 default net initialization, observed through the real simulator: a
// design is elaborated, lowered, and run, then the resolved net value is read
// back from the SimContext.

// 4-state value of bit 0, encoded as (bval << 1) | aval. Canonical Convention
// A: x = (aval=1, bval=1), z = (aval=0, bval=1).
//   0 -> 0, 1 -> 1, z -> 2, x -> 3
uint8_t Bit0(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

constexpr uint8_t kVal1 = 1;
constexpr uint8_t kValZ = 2;
constexpr uint8_t kValX = 3;

// §6.7.1: the default initialization value for a net shall be z.
TEST(NetDefaultValue, UndrivenWireDefaultsToZ) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; wire w; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValZ);
}

// §6.7.1: the default-z rule applies to every non-trireg net type, not just
// `wire`. An undriven `tri` net comes up z as well.
TEST(NetDefaultValue, UndrivenTriDefaultsToZ) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; tri w; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValZ);
}

// §6.7.1: nets with drivers shall assume the output value of their drivers.
TEST(NetDefaultValue, DrivenNetAssumesDriverValue) {
  LowerFixture f;
  auto* var =
      RunAndFindVar("module t; wire w; assign w = 1'b1; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kVal1);
}

// §6.7.1: the default applies to every bit of a vector net, not just bit 0.
// All four bits of an undriven vector wire come up z (aval=0, bval=1 per bit).
TEST(NetDefaultValue, UndrivenVectorWireAllBitsZ) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; wire [3:0] w; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0x0u);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0xFu);
}

// §6.7.1: the trireg net is an exception and shall default to x.
TEST(NetDefaultValue, UndrivenTriregDefaultsToX) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; trireg r; endmodule\n", f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValX);
}

// §6.7.1: the trireg x default also applies across every bit of a vector trireg
// (x is aval=1, bval=1 per bit).
TEST(NetDefaultValue, UndrivenVectorTriregAllBitsX) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; trireg [3:0] r; endmodule\n", f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0xFu);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0xFu);
}

// §6.7.1 (printed page 103 of ~/IEEE 1800-2023.pdf) admits a packed structure
// as a net's data type, `wire addressT w1` reaching a type through a typedef
// name in its own example, and §7.2.1 (printed 147) makes a member of a packed
// structure a window of the vector, `w.opcode` the top eight bits of
// thirty-two. A net declared in a module body carried no layout, so the member
// selects read 0 after `assign w = instr` had driven every bit. 165 is read
// back through the member and through the part-select of the same bits, and
// 0x123456 through the second member: a net with no layout answers 165 to the
// part-select alone and 0 to both members, and a net laid out over the wrong
// bits answers something other than 165 and 0x123456 to them. $bits still
// reports the net's whole width.
TEST(StructNetLayout, TypedefStructWireReadsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  instruction_t instr;\n"
      "  wire instruction_t w;\n"
      "  assign w = instr;\n"
      "  int o, hi, im, nbits;\n"
      "  initial begin\n"
      "    instr.opcode = 8'hA5;\n"
      "    instr.imm = 24'h123456;\n"
      "    #1;\n"
      "    o = w.opcode;\n"
      "    hi = w[31:24];\n"
      "    im = w.imm;\n"
      "    nbits = $bits(w);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* o = f.ctx.FindVariable("o");
  auto* hi = f.ctx.FindVariable("hi");
  auto* im = f.ctx.FindVariable("im");
  auto* nbits = f.ctx.FindVariable("nbits");
  ASSERT_NE(o, nullptr);
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(im, nullptr);
  ASSERT_NE(nbits, nullptr);
  EXPECT_EQ(o->value.ToUint64(), 165u);
  EXPECT_EQ(hi->value.ToUint64(), 165u);
  EXPECT_EQ(im->value.ToUint64(), 0x123456u);
  EXPECT_EQ(nbits->value.ToUint64(), 32u);
}

// The same net declared in a child instance, its type a package's typedef
// made visible by a wildcard import (§26.3): the instance's net is laid out
// under its instance-prefixed name, the one its member selects are resolved
// by, so the child reads 60 and 0xABCDEF back through the members of the
// 0x3CABCDEF the parent drives in. A layout recorded for the top's nets alone,
// or looked up by the bare name from inside the instance, leaves the child
// reading 0 for both members while the part-select still reads 60.
TEST(StructNetLayout, ChildInstanceStructWireReadsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package A;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "endpackage\n"
      "module M(input logic [31:0] bus);\n"
      "  import A::*;\n"
      "  wire instruction_t w;\n"
      "  assign w = bus;\n"
      "  int op, top8, low24;\n"
      "  initial #1 begin\n"
      "    op = w.opcode;\n"
      "    top8 = w[31:24];\n"
      "    low24 = w.imm;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic [31:0] word = 32'h3CABCDEF;\n"
      "  M m(.bus(word));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* op = f.ctx.FindVariable("m.op");
  auto* top8 = f.ctx.FindVariable("m.top8");
  auto* low24 = f.ctx.FindVariable("m.low24");
  ASSERT_NE(op, nullptr);
  ASSERT_NE(top8, nullptr);
  ASSERT_NE(low24, nullptr);
  EXPECT_EQ(op->value.ToUint64(), 60u);
  EXPECT_EQ(top8->value.ToUint64(), 60u);
  EXPECT_EQ(low24->value.ToUint64(), 0xABCDEFu);
}

// §6.7.1's own example writes the structure in the declaration, `wire struct
// packed {logic ecc; logic [7:0] data;} memsig`, naming no typedef at all.
// The nine-bit net is driven with ecc set and data 0x5A, and each member reads
// its own window: 1 and 90. A net with no layout reads 0 for both, and a
// layout with the members in the wrong order reads 0 for ecc and 0xAD for
// data.
TEST(StructNetLayout, AnonymousPackedStructWireReadsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "  assign memsig = {1'b1, 8'h5A};\n"
      "  int e, d;\n"
      "  initial #1 begin\n"
      "    e = memsig.ecc;\n"
      "    d = memsig.data;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e = f.ctx.FindVariable("e");
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(e, nullptr);
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(e->value.ToUint64(), 1u);
  EXPECT_EQ(d->value.ToUint64(), 90u);
}

}  // namespace
