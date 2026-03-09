#include "fixture_elaborator.h"

namespace {

TEST(ElabClause03, Cl3_12_ParameterizedModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("module sub #(parameter W = 8) (\n"
             "    input [W-1:0] a, output [W-1:0] y);\n"
             "  assign y = a;\n"
             "endmodule\n"
             "module top;\n"
             "  wire [15:0] x, y;\n"
             "  sub #(16) u0 (.a(x), .y(y));\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_12_InstantiationWithPortsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inv(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  inv u0(.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_FALSE(design->top_modules[0]->children.empty());
}

TEST(ElabClause03, Cl3_12_ProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial $display(\"test\");\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_12_InterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_12_PackageImportElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  byte_t data;\n"
             "endmodule\n"));
}

}  // namespace
