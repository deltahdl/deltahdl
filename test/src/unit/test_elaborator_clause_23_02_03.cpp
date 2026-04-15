#include "fixture_elaborator.h"

namespace {

TEST(ParameterizedModules, ParameterPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8)(input logic [W-1:0] d);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterizedModules, ParameterDefaultValueResolved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8)();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->params.size(), 1u);
  EXPECT_EQ(top->params[0].name, "W");
  EXPECT_TRUE(top->params[0].is_resolved);
  EXPECT_EQ(top->params[0].resolved_value, 8);
}

TEST(ParameterizedModules, ParameterDependentPortWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8)(input logic [W-1:0] d);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 1u);
  EXPECT_EQ(top->ports[0].width, 8u);
}

TEST(ParameterizedModules, MultipleParametersPreserveOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter MSB = 7, parameter LSB = 0, parameter DEPTH = 4)\n"
      "  (input logic [MSB:LSB] data);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->params.size(), 3u);
  EXPECT_EQ(top->params[0].name, "MSB");
  EXPECT_EQ(top->params[0].resolved_value, 7);
  EXPECT_EQ(top->params[1].name, "LSB");
  EXPECT_EQ(top->params[1].resolved_value, 0);
  EXPECT_EQ(top->params[2].name, "DEPTH");
  EXPECT_EQ(top->params[2].resolved_value, 4);
}

TEST(ParameterizedModules, NonAnsiParameterizedModuleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 4)(a, b);\n"
      "  input [W-1:0] a;\n"
      "  output [W-1:0] b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 2u);
  ASSERT_EQ(top->params.size(), 1u);
  EXPECT_EQ(top->params[0].resolved_value, 4);
}

TEST(ParameterizedModules, LocalparamInPortListIsLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter W = 8, localparam D = W * 2)();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->params.size(), 2u);
  EXPECT_FALSE(top->params[0].is_localparam);
  EXPECT_TRUE(top->params[1].is_localparam);
  EXPECT_EQ(top->params[1].name, "D");
  EXPECT_EQ(top->params[1].resolved_value, 16);
}

TEST(ParameterizedModules, LocalparamDerivedViaShiftExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter num_code_bits = 3,\n"
      "           localparam num_out_bits = 1 << num_code_bits)\n"
      "  (input [num_code_bits-1:0] A,\n"
      "   output reg [num_out_bits-1:0] Y);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->params.size(), 2u);
  EXPECT_EQ(top->params[0].resolved_value, 3);
  EXPECT_EQ(top->params[1].resolved_value, 8);
}

}  // namespace
