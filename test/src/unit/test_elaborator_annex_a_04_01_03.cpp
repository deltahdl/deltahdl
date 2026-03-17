#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProgramInstantiationGrammar, ElaborationProgramInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_prog p0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_prog");
  EXPECT_EQ(top->children[0].inst_name, "p0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

TEST(ProgramInstantiationGrammar, ElaborationProgramInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "program simple_prog(input logic data);\n"
      "endprogram\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_prog u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

TEST(ProgramInstantiationGrammar, ElaborationProgramInstWithParams) {
  ElabFixture f;
  auto* design = Elaborate(
      "program param_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module top;\n"
      "  logic [15:0] d;\n"
      "  param_prog #(.W(16)) u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "param_prog");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

TEST(ProgramInstantiationGrammar, ElaborationProgramInstFromModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "program sub_prog(input logic a);\n"
      "endprogram\n"
      "module top;\n"
      "  logic sig;\n"
      "  sub_prog u0(.a(sig));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "sub_prog");
}

TEST(ProgramInstantiationGrammar, ElaborationMultipleInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  my_prog u0(.clk(clk)), u1(.clk(clk));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].module_name, "my_prog");
  EXPECT_EQ(top->children[0].inst_name, "u0");
  EXPECT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].module_name, "my_prog");
  EXPECT_EQ(top->children[1].inst_name, "u1");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(ProgramInstantiationGrammar, ElaborationUnresolvedProgram) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  nonexistent_prog u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

}  // namespace
