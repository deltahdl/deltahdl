#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

uint8_t Bit0(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

constexpr uint8_t kVal1 = 1;
constexpr uint8_t kValZ = 2;
constexpr uint8_t kValX = 3;

TEST(NetDefaultValue, UndrivenWireDefaultsToZ) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; wire w; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValZ);
}

TEST(NetDefaultValue, UndrivenTriDefaultsToZ) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; tri w; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValZ);
}

TEST(NetDefaultValue, DrivenNetAssumesDriverValue) {
  LowerFixture f;
  auto* var =
      RunAndFindVar("module t; wire w; assign w = 1'b1; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kVal1);
}

TEST(NetDefaultValue, UndrivenVectorWireAllBitsZ) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; wire [3:0] w; endmodule\n", f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0x0u);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0xFu);
}

TEST(NetDefaultValue, UndrivenTriregDefaultsToX) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; trireg r; endmodule\n", f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValX);
}

TEST(NetDefaultValue, UndrivenVectorTriregAllBitsX) {
  LowerFixture f;
  auto* var = RunAndFindVar("module t; trireg [3:0] r; endmodule\n", f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0xFu);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0xFu);
}

TEST(NetDefaultValue, NetTypeKeywordBeforeADataTypeDecidesResolution) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  tri0 logic n0;\n"
                       "  tri1 logic [3:0] n1;\n"
                       "  wand logic w;\n"
                       "  assign w = 1'b1;\n"
                       "  assign w = 1'b0;\n"
                       "  initial #1 $display(\"%b %b %b\", n0, n1, w);\n"
                       "endmodule\n",
                       f),
            "0 1111 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

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

TEST(NetDefaultValue, NetsOfFourStateTypesTakeTheirWidthsAndStartAtZOrTriregX) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  trireg (large) logic #(0, 0, 0) cap1;\n"
      "  typedef logic [31:0] addressT;\n"
      "  wire addressT w1;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "  initial #1 $display(\"%b %v %0d %0d %b %b\", cap1, cap1, $bits(w1),\n"
      "                      $bits(memsig), w1[31:28], memsig);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x LaX 32 9 zzzz zzzzzzzzz\n");
}

}  // namespace
