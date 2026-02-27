// §11.4.9: Reduction operators

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_eval_op.h"

using namespace delta;

namespace {

TEST(EvalOp, LtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(EvalOp, GtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// ==========================================================================
// Reduction X/Z propagation — §11.4.9
// ==========================================================================
TEST(EvalOpXZ, ReductionAndWithX) {
  SimFixture f;
  // &4'b1x11 → x (not all bits known-1)
  MakeVar4(f, "ra", 4, 0b1011, 0b0100);  // bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ra"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalOpXZ, ReductionAndWithKnown0) {
  SimFixture f;
  // &4'b0x11 → 0 (known-0 bit forces result to 0)
  MakeVar4(f, "rb", 4, 0b0011, 0b0100);  // bit3=0, bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);  // known-0
}

TEST(EvalOpXZ, ReductionOrWithKnown1) {
  SimFixture f;
  // |4'b1x00 → 1 (known-1 bit forces result to 1)
  MakeVar4(f, "rc", 4, 0b1000, 0b0100);  // bit3=1, bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rc"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);  // known-1
}

TEST(EvalOpXZ, ReductionOrWithX) {
  SimFixture f;
  // |4'b0x00 → x (no known-1, but X could be 1)
  MakeVar4(f, "rd", 4, 0b0000, 0b0100);  // all 0 except bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalOpXZ, ReductionXorWithX) {
  SimFixture f;
  // ^4'b1x10 → x (any X/Z in XOR → X)
  MakeVar4(f, "re", 4, 0b1010, 0b0100);  // bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "re"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

// § expression — reduction AND
TEST(SimA83, ReductionAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = &8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § expression — reduction OR
TEST(SimA83, ReductionOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = |8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction AND
TEST(SimA86, UnaryReductionAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = &8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — reduction NAND
TEST(SimA86, UnaryReductionNand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~&8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction OR
TEST(SimA86, UnaryReductionOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = |8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction NOR
TEST(SimA86, UnaryReductionNor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~|8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — reduction XOR
TEST(SimA86, UnaryReductionXor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ^8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // A5 = 10100101, popcount=4 (even), XOR reduction = 0
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// § unary_operator — reduction XNOR (~^)
TEST(SimA86, UnaryReductionXnor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~^8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // ~^(A5) = ~(XOR reduction) = ~0 = 1
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § unary_operator — reduction XNOR (^~)
TEST(SimA86, UnaryReductionXnorAlt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ^~8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
