#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VectorSpecification, LittleEndianWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [0:7] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, ThirtyTwoBitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [31:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

TEST(VectorSpecification, NetAndVarSameWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [15:0] net_w;\n"
      "  logic [15:0] var_v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 16u);
  EXPECT_EQ(mod->variables[0].width, 16u);
}

TEST(VectorSpecification, NegativeRangeWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [-1:4] b; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 6u);
}

TEST(VectorSpecification, EqualMsbLsbWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [3:3] a; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(VectorSpecification, BitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit [7:0] b; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, RegVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; reg [7:0] r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, ConstantExpressionRange) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [2+1:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, BothNegativeRangeWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [-1:-4] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, GuaranteedMinimumMaxLength) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [65535:0] big; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 65536u);
}

TEST(VectorSpecification, ParameterConstantRange) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; parameter P = 4; logic [P-1:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, LocalparamConstantRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m; localparam int HI = 5; localparam int LO = 2; logic [HI:LO] "
      "v; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(VectorSpecification, ConstantFunctionCallRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function automatic int w(); return 8; endfunction\n"
      "  logic [w()-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VectorSpecification, XInRangeIsError) {
  ElabFixture f;
  Elaborate("module m; logic [1'bx:0] a; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            1, "7.4.1"));
}

TEST(VectorSpecification, ZInRangeIsError) {
  ElabFixture f;
  Elaborate("module m; logic [1'bz:0] a; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            1, "7.4.1"));
}

}  // namespace
