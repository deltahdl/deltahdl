#include <gtest/gtest.h>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

namespace {

TEST(PackageImportInHeader, TypedefVisibleInPortType) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m import pkg::byte_t; (input byte_t a, output byte_t b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, WildcardTypedefVisibleInPortType) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [15:0] word_t;\n"
             "endpackage\n"
             "module m import pkg::*; (input word_t a, output word_t b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ConstantVisibleInPortRange) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int W = 8;\n"
             "endpackage\n"
             "module m import pkg::W; (input [W-1:0] a, output [W-1:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ConstantVisibleInParameterDefault) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int DEFAULT_W = 16;\n"
             "endpackage\n"
             "module m import pkg::DEFAULT_W; #(parameter int W = DEFAULT_W) "
             "(input [W-1:0] a);\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, WildcardImportVisibleInBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "endpackage\n"
      "module m import pkg::*; ();\n"
      "  nibble_t n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* n = FindVar(design, "m", "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 4u);
}

TEST(PackageImportInHeader, ExplicitImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic signed [31:0] sword_t;\n"
             "endpackage\n"
             "module m import pkg::sword_t; ();\n"
             "  sword_t s;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, MultipleHeaderImports) {
  EXPECT_TRUE(
      ElabOk("package a;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "package b;\n"
             "  parameter int N = 4;\n"
             "endpackage\n"
             "module m import a::byte_t, b::N; (input byte_t [N-1:0] data);\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, InterfaceHeaderImportVisibleInBody) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "interface ifc import pkg::*; ();\n"
             "  byte_t data;\n"
             "endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, InterfaceHeaderImportVisibleInPortType) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "interface ifc import pkg::byte_t; (input byte_t a);\n"
      "  byte_t shadow;\n"
      "  assign shadow = a;\n"
      "endinterface\n",
      f, "ifc");
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImportInHeader, MixedExplicitAndWildcardHeaderImports) {
  EXPECT_TRUE(
      ElabOk("package A;\n"
             "  typedef logic [7:0] opcode_t;\n"
             "endpackage\n"
             "package B;\n"
             "  typedef logic flag_t;\n"
             "endpackage\n"
             "module m import A::opcode_t, B::*; #(parameter int WIDTH = 4)\n"
             "    (input opcode_t a, output flag_t ok);\n"
             "  assign ok = |a;\n"
             "endmodule\n"));
}

TEST(PackageImportInHeader, ProgramHeaderImportVisibleInPortAndBody) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "program p import pkg::byte_t; (input byte_t a);\n"
      "  byte_t local_b;\n"
      "  initial local_b = a;\n"
      "endprogram\n",
      f, "p");
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImportInHeader, WildcardProgramHeaderImportVisibleInPort) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n"
      "program p import pkg::*; (input word_t a, output word_t b);\n"
      "  initial b = a;\n"
      "endprogram\n",
      f, "p");
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImportInHeader, WildcardImportedStructNetPortCarriesItsLayout) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package A;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "endpackage\n"
      "module M import A::*; (input instruction_t a);\n"
      "endmodule\n"
      "module top;\n"
      "  A::instruction_t instr;\n"
      "  M m(.a(instr));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindVar(design, "M", "a"), nullptr);
  const auto* m = FindModule(design, "M");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 1u);
  const RtlirPort& a = m->ports[0];
  EXPECT_EQ(a.name, "a");
  EXPECT_FALSE(a.is_var);
  EXPECT_EQ(a.net_type, NetType::kWire);
  EXPECT_EQ(a.width, 32u);
  ASSERT_NE(a.dtype, nullptr);
  ASSERT_EQ(a.dtype->struct_members.size(), 2u);
  EXPECT_EQ(a.dtype->struct_members[0].name, "opcode");
  EXPECT_EQ(a.dtype->struct_members[1].name, "imm");
}

TEST(PackageImportInHeader,
     NamedImportedStructPortOfTheTopDeclaresItsVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package A;\n"
      "  typedef struct packed { bit [7:0] opcode; bit [23:0] addr; } "
      "instruction_t;\n"
      "endpackage\n"
      "package B;\n"
      "  typedef enum bit { FALSE, TRUE } boolean_t;\n"
      "endpackage\n"
      "module M import A::instruction_t, B::*;\n"
      "  #(WIDTH = 32)\n"
      "  (input [WIDTH-1:0] data, output instruction_t a, output boolean_t OK);"
      "\n"
      "  assign OK = TRUE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* a = FindVar(design, "M", "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->width, 32u);
  EXPECT_FALSE(a->is_4state);
  ASSERT_NE(a->dtype, nullptr);
  EXPECT_EQ(a->dtype->struct_members.size(), 2u);
  EXPECT_EQ(FindVar(design, "M", "data"), nullptr);
  EXPECT_EQ(FindVar(design, "M", "OK"), nullptr);
}

}  // namespace
