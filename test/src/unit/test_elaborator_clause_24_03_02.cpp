#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ProgramPortElab, ProgramInstanceInModuleResolvesToProgramScope) {
  ElabFixture f;
  auto* design = Elaborate(
      "program p(output logic [7:0] pw_out, input logic [7:0] pw_in);\n"
      "endprogram\n"
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  p p_i(.pw_out(b), .pw_in(a));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  EXPECT_FALSE(top->is_program);
  ASSERT_GE(top->children.size(), 1u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_TRUE(top->children[0].resolved->is_program);
}

TEST(ProgramPortElab, ProgramPortBindingsTargetDesignSignals) {
  ElabFixture f;
  auto* design = Elaborate(
      "program p(output logic [7:0] pw_out, input logic [7:0] pw_in);\n"
      "endprogram\n"
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  p p_i(.pw_out(b), .pw_in(a));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  const auto& inst = top->children[0];
  ASSERT_EQ(inst.port_bindings.size(), 2u);
  bool saw_out = false;
  bool saw_in = false;
  for (const auto& binding : inst.port_bindings) {
    ASSERT_NE(binding.connection, nullptr);
    if (binding.port_name == "pw_out") {
      saw_out = true;
      EXPECT_EQ(binding.connection->text, "b");
    } else if (binding.port_name == "pw_in") {
      saw_in = true;
      EXPECT_EQ(binding.connection->text, "a");
    }
  }
  EXPECT_TRUE(saw_out);
  EXPECT_TRUE(saw_in);
}

TEST(ProgramPortElab, ProgramOutputPortConnectsToDesignWire) {
  ElabFixture f;
  auto* design = Elaborate(
      "program p(output logic [3:0] pw);\n"
      "endprogram\n"
      "module top;\n"
      "  wire [3:0] w;\n"
      "  p p_i(.pw(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  EXPECT_FALSE(top->is_program);
  ASSERT_GE(top->children.size(), 1u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_TRUE(top->children[0].resolved->is_program);
  ASSERT_EQ(top->children[0].port_bindings.size(), 1u);
  ASSERT_NE(top->children[0].port_bindings[0].connection, nullptr);
  EXPECT_EQ(top->children[0].port_bindings[0].connection->text, "w");
}

TEST(ProgramPortElab, ProgramInoutPortConnectsToDesignWire) {
  ElabFixture f;
  auto* design = Elaborate(
      "program p(inout wire [3:0] pw);\n"
      "endprogram\n"
      "module top;\n"
      "  wire [3:0] w;\n"
      "  p p_i(.pw(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_TRUE(top->children[0].resolved->is_program);
}

TEST(ProgramPortElab, MultipleProgramInstancesAllHaveProgramScope) {
  ElabFixture f;
  auto* design = Elaborate(
      "program p(input logic x);\n"
      "endprogram\n"
      "module top;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  p p0(.x(a));\n"
      "  p p1(.x(b));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  EXPECT_FALSE(top->is_program);
  ASSERT_EQ(top->children.size(), 2u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  ASSERT_NE(top->children[1].resolved, nullptr);
  EXPECT_TRUE(top->children[0].resolved->is_program);
  EXPECT_TRUE(top->children[1].resolved->is_program);
}

TEST(ProgramPortElab, NestedProgramInModuleRetainsProgramScope) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial v = 8'd1;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  EXPECT_FALSE(top->is_program);
  ASSERT_GE(top->children.size(), 1u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_TRUE(top->children[0].resolved->is_program);
}

TEST(ProgramPortElab, PositionalProgramPortBindingsResolve) {
  ElabFixture f;
  auto* design = Elaborate(
      "program p(output logic [7:0] pw_out, input logic [7:0] pw_in);\n"
      "endprogram\n"
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  p p_i(b, a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  const auto& inst = top->children[0];
  ASSERT_EQ(inst.port_bindings.size(), 2u);
  for (const auto& binding : inst.port_bindings) {
    ASSERT_NE(binding.connection, nullptr);
  }
}

}  // namespace
