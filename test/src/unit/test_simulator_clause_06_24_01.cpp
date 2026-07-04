#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CastOperatorSim, IntCastFromReal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = int'(4.0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(CastOperatorSim, SizeCastPadsNarrowToWide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = int'(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(CastOperatorSim, SizeCastSameWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 32'h12345678;\n"
      "    result = int'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x12345678u);
}

TEST(CastOperatorSim, LongintCastPads) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint result;\n"
      "  initial result = longint'(32'hDEADBEEF);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(CastOperatorSim, VoidCastDiscardsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    void'(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CastOperatorSim, ConstCastPreservesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial result = const'(99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CastOperatorSim, UnsignedCastOfNegativeFour) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] regA;\n"
      "  initial regA = unsigned'(-4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("regA");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(CastOperatorSim, SignedCastOfFourBitVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] regS;\n"
      "  initial regS = signed'(4'b1100);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

// 6.24.1: when the casting type is a constant expression giving a positive
// width, the operand is truncated to that width. A numeric size cast narrower
// than its operand (4'(8'hAB)) keeps only the low four bits, 0xB.
TEST(CastOperatorSim, NumericSizeCastTruncates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  initial r = 4'(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

// 6.24.1: the size given by a numeric size cast may come from any constant
// expression, including a parameter (a constant form of 11.2.1). Driving the
// width through a parameter and running the design shows the parameter's value
// selects the truncation width just as a literal does.
TEST(CastOperatorSim, NumericSizeCastParameterWidthTruncates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter N = 4;\n"
      "  logic [7:0] r;\n"
      "  initial r = N'(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

// 6.24.1: a size cast returns the value a packed [n-1:0] vector would hold
// after being assigned the operand, and the operand's own signedness passes
// through unchanged. Widening a signed operand therefore sign-extends it: the
// signed four-bit value 1100 (-4) cast to eight bits is 8'hFC, not 8'h0C.
TEST(CastOperatorSim, NumericSizeCastSignExtendsSignedOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 4'sb1100;\n"
      "    r = 8'(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

// 6.24.1: the signedness that passes through is the operand's own, so widening
// an unsigned operand zero-extends rather than sign-extends -- the same four
// low bits 1111 cast to eight bits is 8'h0F, contrasting with the signed case.
TEST(CastOperatorSim, NumericSizeCastZeroExtendsUnsignedOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    u = 4'b1111;\n"
      "    r = 8'(u);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// 6.24.1: a size given by a localparam (another constant form of 11.2.1)
// selects the truncation width at run time exactly as a literal or parameter
// does. Built from real localparam syntax and driven through the full pipeline.
TEST(CastOperatorSim, NumericSizeCastLocalparamWidthTruncates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam N = 4;\n"
      "  logic [7:0] r;\n"
      "  initial r = N'(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(CastOperatorSim, IntCastFromRealRoundsHalfUp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial result = int'(2.5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

}  // namespace
