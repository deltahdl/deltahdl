#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(AdditionBitLength, SameWidthLhsDropsCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumA = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumA");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

TEST(AdditionBitLength, WiderLhsPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(AdditionBitLength, ContinuousAssignWiderLhsPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  wire  [16:0] sumB;\n"
      "  assign sumB = a + b;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(AdditionBitLength, NonblockingAssignWiderLhsPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB <= a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(AdditionBitLength, SingleBitOperandsCarryIntoTwoBitLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  logic [1:0] sumB;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x2u);
}

// Operand-kind coverage: the addends are sized 16-bit literals rather than
// variables. The assignment's 17-bit target must still set the width the '+'
// is evaluated at, so the carry-out lands in bit 16 instead of being truncated
// away at the operands' own 16-bit width.
TEST(AdditionBitLength, LiteralOperandsWiderLhsPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [16:0] sumB;\n"
      "  initial sumB = 16'hFFFF + 16'h0001;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// Syntactic-position coverage: a declaration initializer is an assignment, so
// the initialized variable's 17-bit width is the context the '+' is evaluated
// in -- the carry-out must survive here just as it does for the procedural,
// continuous, and nonblocking forms above. Self-determined evaluation at the
// operands' 16-bit width would instead zero the result.
TEST(AdditionBitLength, DeclarationInitializerWiderLhsPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [16:0] sumB = 16'hFFFF + 16'h0001;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

}  // namespace
