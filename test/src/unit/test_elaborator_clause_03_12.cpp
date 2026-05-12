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
