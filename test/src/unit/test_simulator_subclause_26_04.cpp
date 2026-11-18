#include <gtest/gtest.h>

#include <string>

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

constexpr const char* kHeaderPackages =
    "package p; typedef logic [5:0] six_t; parameter int W = 5; "
    "typedef enum {E0, E1, E2} e_t; endpackage\n"
    "package pkg; typedef logic [7:0] byte_t; typedef logic [15:0] word_t; "
    "parameter int W = 5; endpackage\n";

void ExpectHeaderOutput(const std::string& src, const std::string& expected) {
  SCOPED_TRACE(src);
  SimFixture f;
  EXPECT_EQ(RunCapture(kHeaderPackages + src, f), expected);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackageImportInHeaderSim, ExplicitlyImportedTypedefSizesABodyVariable) {
  ExpectHeaderOutput(
      "module top import p::six_t; (); six_t x; "
      "initial $display(\"%0d\", $bits(x)); endmodule\n",
      "6\n");
}

TEST(PackageImportInHeaderSim, ImportedConstantSizesAnAnsiPortRange) {
  ExpectHeaderOutput(
      "module m import p::*; (input [W-1:0] a); "
      "initial $display(\"%0d\", $bits(a)); endmodule\n"
      "module top; m u(5'd0); endmodule\n",
      "5\n");
}

TEST(PackageImportInHeaderSim, ImportedConstantIsAParameterPortsDefault) {
  ExpectHeaderOutput(
      "module top import p::*; #(parameter int N = W) (); "
      "initial $display(\"%0d\", N); endmodule\n",
      "5\n");
}

TEST(PackageImportInHeaderSim, ImportedLiteralIsAnUnconnectedPortsDefault) {
  ExpectHeaderOutput(
      "module m import p::*; (input var e_t e = E2); "
      "initial #1 $display(\"%0d\", e); endmodule\n"
      "module top; m u(); endmodule\n",
      "2\n");
}

TEST(PackageImportInHeaderSim, ImportedTypeOnAParameterAndATypeParameter) {
  ExpectHeaderOutput(
      "module top import p::*; #(parameter six_t P = 6'd63, "
      "parameter type T = six_t) (); T t; "
      "initial $display(\"%0d %0d\", P, $bits(t)); endmodule\n",
      "63 6\n");
}

TEST(PackageImportInHeaderSim, ImportedTypeOnANonAnsiPortDeclaredInTheBody) {
  ExpectHeaderOutput(
      "module m import p::*; (a); input six_t a; "
      "initial $display(\"%0d\", $bits(a)); endmodule\n"
      "module top; m u(6'd0); endmodule\n",
      "6\n");
}

TEST(PackageImportInHeaderSim, InterfaceHeaderImportsSizeItsBodyAndPorts) {
  ExpectHeaderOutput(
      "interface ifc import pkg::*; (); byte_t data; endinterface\n"
      "module top; ifc i(); initial $display(\"%0d\", $bits(i.data)); "
      "endmodule\n",
      "8\n");
  ExpectHeaderOutput(
      "interface ifc import pkg::byte_t; (input byte_t a); byte_t shadow; "
      "initial $display(\"%0d %0d\", $bits(a), $bits(shadow)); "
      "endinterface\n"
      "module top; ifc i(8'd0); endmodule\n",
      "8 8\n");
  ExpectHeaderOutput(
      "interface ifc import pkg::*; #(parameter int N = W) (); "
      "initial $display(\"%0d\", N); endinterface\n"
      "module top; ifc i(); endmodule\n",
      "5\n");
}

TEST(PackageImportInHeaderSim, ProgramHeaderImportsSizeItsBodyAndPorts) {
  ExpectHeaderOutput(
      "program pg import pkg::byte_t; (input byte_t a); byte_t local_b; "
      "initial $display(\"%0d %0d\", $bits(a), $bits(local_b)); "
      "endprogram\n"
      "module top; pg u(8'd0); endmodule\n",
      "8 8\n");
  ExpectHeaderOutput(
      "program pg import pkg::*; (input word_t a, output word_t b); "
      "initial $display(\"%0d %0d\", $bits(a), $bits(b)); endprogram\n"
      "module top; logic [15:0] y; pg u(16'd0, y); endmodule\n",
      "16 16\n");
  ExpectHeaderOutput(
      "program pg import pkg::*; #(parameter int N = W) (input [W-1:0] a); "
      "initial $display(\"%0d %0d\", N, $bits(a)); endprogram\n"
      "module top; pg u(5'd0); endmodule\n",
      "5 5\n");
}

TEST(PackageImportInHeaderSim, HeaderWithALifetimeOrAnAttribute) {
  ExpectHeaderOutput(
      "module automatic top import p::*; #(parameter int N = W) (); "
      "initial $display(\"%0d %0d\", N, $bits(six_t)); endmodule\n",
      "5 6\n");
  ExpectHeaderOutput(
      "interface automatic ifc import p::*; #(parameter int N = W) (); "
      "initial $display(\"%0d\", N); endinterface\n"
      "module top; ifc i(); endmodule\n",
      "5\n");
  ExpectHeaderOutput(
      "program automatic pg import p::*; #(parameter int N = W) (); "
      "initial $display(\"%0d\", N); endprogram\n"
      "module top; pg u(); endmodule\n",
      "5\n");
  ExpectHeaderOutput(
      "(* foo *) interface automatic ifc import p::*; "
      "#(parameter int N = W); initial $display(\"%0d\", N); "
      "endinterface\n"
      "module top; ifc i(); endmodule\n",
      "5\n");
}

TEST(PackageImportInHeaderSim, MacromoduleHeaderImport) {
  ExpectHeaderOutput(
      "macromodule top import p::*; (); six_t x; "
      "initial $display(\"%0d %0d\", $bits(x), W); endmodule\n",
      "6 5\n");
}

}  // namespace
