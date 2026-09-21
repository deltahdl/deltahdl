#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PackageImportInHeaderSim, ConstantFromHeaderImportSetsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 42;\n"
      "endpackage\n"
      "module t import pkg::VAL; ();\n"
      "  logic [7:0] x;\n"
      "  initial x = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 42u);
}

TEST(PackageImportInHeaderSim, WildcardConstantFromHeaderImport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 7;\n"
      "endpackage\n"
      "module t import pkg::*; ();\n"
      "  logic [7:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 7u);
}

// §26.4 (printed page 812 of IEEE 1800-2023) has a header import make a
// package's names visible in the port list, its own example typing `input
// instruction_t a` through `import A::instruction_t`, and §7.2.1 makes a member
// of a packed structure a window of the variable's bits, `a.opcode` the top
// eight of thirty-two. The port's storage was created with no layout, so
// `a.opcode` read a one-bit 0 after the parent wrote the connected variable's
// members. 165 and 0x123456 are read back through the member, the part-select
// of the same bits and the second member: a one-bit port answers 0 or 1 to
// each, and a port sized without a layout answers 165 to the part-select alone.
TEST(PackageImportInHeaderSim, WildcardImportedStructPortReadsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package A;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "endpackage\n"
      "module M import A::*; (input instruction_t a);\n"
      "  int o, hi, im;\n"
      "  initial #1 begin\n"
      "    o = a.opcode;\n"
      "    hi = a[31:24];\n"
      "    im = a.imm;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  A::instruction_t instr;\n"
      "  M m(.a(instr));\n"
      "  initial begin\n"
      "    instr.opcode = 8'hA5;\n"
      "    instr.imm = 24'h123456;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* o = f.ctx.FindVariable("m.o");
  auto* hi = f.ctx.FindVariable("m.hi");
  auto* im = f.ctx.FindVariable("m.im");
  ASSERT_NE(o, nullptr);
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(im, nullptr);
  EXPECT_EQ(o->value.ToUint64(), 165u);
  EXPECT_EQ(hi->value.ToUint64(), 165u);
  EXPECT_EQ(im->value.ToUint64(), 0x123456u);
}

// The top's own port list, through the explicit form of §26.4's example with
// its parameter port list: a member write to the output port lands in the
// member's bits and the whole port reads the two members side by side. The
// members are `bit`, so the port is 2-state and reads 0xA5123456 whole rather
// than an x-filled value: a port written through a one-bit variable would hold
// 1 and a port with no layout 0.
TEST(PackageImportInHeaderSim, NamedImportedStructPortOfTheTopHoldsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package A;\n"
      "  typedef struct packed { bit [7:0] opcode; bit [23:0] addr; } "
      "instruction_t;\n"
      "endpackage\n"
      "package B;\n"
      "  typedef enum bit { FALSE, TRUE } boolean_t;\n"
      "endpackage\n"
      "module t import A::instruction_t, B::*;\n"
      "  #(WIDTH = 32)\n"
      "  (output instruction_t r, output boolean_t OK);\n"
      "  int o;\n"
      "  assign OK = TRUE;\n"
      "  initial begin\n"
      "    r.opcode = 8'hA5;\n"
      "    r.addr = 24'h123456;\n"
      "    o = r.opcode;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("r");
  auto* o = f.ctx.FindVariable("o");
  auto* ok = f.ctx.FindVariable("OK");
  ASSERT_NE(r, nullptr);
  ASSERT_NE(o, nullptr);
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(r->value.width, 32u);
  EXPECT_EQ(r->value.ToUint64(), 0xA5123456u);
  EXPECT_EQ(o->value.ToUint64(), 165u);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
}

}  // namespace
