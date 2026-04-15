#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, ParameterizedModuleElaborates) {
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

TEST(DesignBuildingBlockElaboration, InstantiationWithPortsElaborates) {
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

TEST(DesignBuildingBlockElaboration, ProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial $display(\"test\");\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignBuildingBlockElaboration, InterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignBuildingBlockElaboration, PackageImportElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  byte_t data;\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, ElaborationComputesParameterValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub #(parameter W = 8)(input [W-1:0] a, output [W-1:0] y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [15:0] x, y;\n"
      "  sub #(16) u0 (.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_FALSE(child->params.empty());
  EXPECT_EQ(child->params[0].resolved_value, 16);
  EXPECT_TRUE(child->params[0].is_resolved);
}

TEST(DesignBuildingBlockElaboration, MultiLevelHierarchyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module mid(input logic a, output logic y);\n"
      "  leaf u0(.a(a), .y(y));\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  mid u0(.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "mid");
  auto* mid = top->children[0].resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_EQ(mid->children.size(), 1u);
  EXPECT_EQ(mid->children[0].module_name, "leaf");
}

TEST(DesignBuildingBlockElaboration, ElaborationEstablishesPortBindings) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub(input logic a, b, output logic y);\n"
      "  assign y = a & b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x1, x2, out;\n"
      "  sub u0(.a(x1), .b(x2), .y(out));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings.size(), 3u);
}

TEST(DesignBuildingBlockElaboration, UnresolvedModuleIsError) {
  EXPECT_FALSE(
      ElabOk("module top;\n"
             "  nonexistent u0();\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, ParameterDefaultValueElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub #(parameter W = 8)(input [W-1:0] a, output [W-1:0] y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] x, y;\n"
      "  sub u0 (.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_FALSE(child->params.empty());
  EXPECT_EQ(child->params[0].resolved_value, 8);
}

}  // namespace
