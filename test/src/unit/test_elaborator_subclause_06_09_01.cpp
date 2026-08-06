

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

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

// §6.9.1: the range rule applies to reg, logic, and bit vectors alike. reg is
// the third enumerated element type (logic and bit are covered above), so a
// ranged reg declaration must elaborate to the width of its span.
TEST(VectorSpecification, RegVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; reg [7:0] r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.9.1: the range bounds are constant integer expressions, not just literals.
// The elaborator folds an arithmetic bound expression before computing width.
TEST(VectorSpecification, ConstantExpressionRange) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [2+1:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

// §6.9.1: range bounds may be any integer value, including negative on both
// ends; the width is the magnitude of the span plus one.
TEST(VectorSpecification, BothNegativeRangeWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [-1:-4] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

// §6.9.1: implementations may cap the maximum vector length, but the cap shall
// be no smaller than 2**16 bits. A vector at exactly that guaranteed minimum
// must elaborate without error and carry its full declared width.
TEST(VectorSpecification, GuaranteedMinimumMaxLength) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [65535:0] big; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 65536u);
}

// §6.9.1: the msb/lsb bounds shall be constant integer expressions (see
// 11.2.1). A parameter is one of the constant forms 11.2.1 admits, so a range
// built from a parameter reference must fold to the same width as the literal
// range it stands for.
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

// §6.9.1: a localparam is likewise a constant form of 11.2.1. Here both bounds
// are localparam references, so the width comes from folding both constant
// expressions and taking the span.
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

// §6.9.1: a constant function call is another constant form of 11.2.1 that a
// range bound may use. The elaborator evaluates the call at elaboration time to
// obtain the bound before computing the vector width.
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
  EXPECT_TRUE(f.has_errors);
}

TEST(VectorSpecification, ZInRangeIsError) {
  ElabFixture f;
  Elaborate("module m; logic [1'bz:0] a; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
