#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalOpXZ, ReductionAndWithX) {
  SimFixture f;

  MakeVar4(f, "ra", 4, 0b1011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ra"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionAndWithKnown0) {
  SimFixture f;

  MakeVar4(f, "rb", 4, 0b0011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithKnown1) {
  SimFixture f;

  MakeVar4(f, "rc", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rc"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithX) {
  SimFixture f;

  MakeVar4(f, "rd", 4, 0b0000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXorWithX) {
  SimFixture f;

  MakeVar4(f, "re", 4, 0b1010, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "re"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(OperatorSim, UnaryReductionAnd) {
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

TEST(OperatorSim, UnaryReductionNand) {
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

TEST(OperatorSim, UnaryReductionOr) {
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

TEST(OperatorSim, UnaryReductionNor) {
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

TEST(OperatorSim, UnaryReductionXor) {
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

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, UnaryReductionXnor) {
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

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnaryReductionXnorAlt) {
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

TEST(EvalOp, ReductionAndAllOnes) {
  SimFixture f;

  auto* expr =
      MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0xFFFFFFFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionAndNotAllOnes) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionOrNonZero) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionOrZero) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorEvenOnes) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorOddOnes) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNand) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNor) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorTildeCaret) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorCaretTilde) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kCaretTilde, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionAndZero) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// --- z-input reduction: AND ---

TEST(EvalOpXZ, ReductionAndWithZKnown0) {
  SimFixture f;
  // 4'b0z10: known-0 in bit 3 dominates → result is 0.
  MakeVar4(f, "v", 4, 0b0110, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionAndWithZNoKnown0) {
  SimFixture f;
  // 4'b1z11: no known-0 bit → result is unknown.
  MakeVar4(f, "v", 4, 0b1111, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// --- z-input reduction: OR ---

TEST(EvalOpXZ, ReductionOrWithZKnown1) {
  SimFixture f;
  // 4'b1z00: known-1 in bit 3 dominates → result is 1.
  MakeVar4(f, "v", 4, 0b1100, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithZNoKnown1) {
  SimFixture f;
  // 4'b0z00: no known-1 bit → result is unknown.
  MakeVar4(f, "v", 4, 0b0100, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// --- z-input reduction: XOR ---

TEST(EvalOpXZ, ReductionXorWithZ) {
  SimFixture f;
  // 4'b1z10: z bit present → result is unknown.
  MakeVar4(f, "v", 4, 0b1110, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// --- x-input reduction: NAND/NOR/XNOR ---

TEST(EvalOpXZ, ReductionNandWithXNoKnown0) {
  SimFixture f;
  // 4'b1x11: AND gives x → NAND gives x.
  MakeVar4(f, "v", 4, 0b1011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNandWithXKnown0) {
  SimFixture f;
  // 4'b0x11: AND gives 0 → NAND gives 1.
  MakeVar4(f, "v", 4, 0b0011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNorWithXKnown1) {
  SimFixture f;
  // 4'b1x00: OR gives 1 → NOR gives 0.
  MakeVar4(f, "v", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNorWithXNoKnown1) {
  SimFixture f;
  // 4'b0x00: OR gives x → NOR gives x.
  MakeVar4(f, "v", 4, 0b0000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXnorWithX) {
  SimFixture f;
  // 4'b1x10: XOR gives x → XNOR gives x.
  MakeVar4(f, "v", 4, 0b1010, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// --- z-input reduction: NAND/NOR/XNOR ---

TEST(EvalOpXZ, ReductionNandWithZ) {
  SimFixture f;
  // 4'b1z11: AND gives x → NAND gives x.
  MakeVar4(f, "v", 4, 0b1111, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNorWithZ) {
  SimFixture f;
  // 4'b0z00: OR gives x → NOR gives x.
  MakeVar4(f, "v", 4, 0b0100, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXnorWithZ) {
  SimFixture f;
  // 4'b1z10: XOR gives x → XNOR gives x.
  MakeVar4(f, "v", 4, 0b1110, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// --- Result width is always 1 bit ---

TEST(EvalOp, ReductionAndResultIsOneBit) {
  SimFixture f;
  auto* expr =
      MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0xFFFFFFFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionOrResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionXorResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionNandResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionNorResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionXnorResultIsOneBit) {
  SimFixture f;
  auto* expr =
      MakeUnary(f.arena, TokenKind::kTildeCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// --- Table 11-19: systematic coverage ---

TEST(EvalOp, Table1119_NoBitsSet) {
  SimFixture f;
  // 4'b0000: &→0  ~&→1  |→0  ~|→1  ^→0  ~^→1
  MakeVar4(f, "v", 4, 0b0000, 0);
  auto id = [&]() { return MakeId(f.arena, "v"); };

  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kAmp, id()), f.ctx, f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeAmp, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kPipe, id()), f.ctx, f.arena)
          .ToUint64(),
      0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildePipe, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kCaret, id()), f.ctx, f.arena)
          .ToUint64(),
      0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeCaret, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
}

TEST(EvalOp, Table1119_AllBitsSet) {
  SimFixture f;
  // 4'b1111: &→1  ~&→0  |→1  ~|→0  ^→0  ~^→1
  MakeVar4(f, "v", 4, 0b1111, 0);
  auto id = [&]() { return MakeId(f.arena, "v"); };

  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kAmp, id()), f.ctx, f.arena)
                .ToUint64(),
            1u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeAmp, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kPipe, id()), f.ctx, f.arena)
          .ToUint64(),
      1u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildePipe, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kCaret, id()), f.ctx, f.arena)
          .ToUint64(),
      0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeCaret, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
}

TEST(EvalOp, Table1119_EvenBitsSet) {
  SimFixture f;
  // 4'b0110: &→0  ~&→1  |→1  ~|→0  ^→0  ~^→1
  MakeVar4(f, "v", 4, 0b0110, 0);
  auto id = [&]() { return MakeId(f.arena, "v"); };

  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kAmp, id()), f.ctx, f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeAmp, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kPipe, id()), f.ctx, f.arena)
          .ToUint64(),
      1u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildePipe, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kCaret, id()), f.ctx, f.arena)
          .ToUint64(),
      0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeCaret, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
}

TEST(EvalOp, Table1119_OddBitsSet) {
  SimFixture f;
  // 4'b1000: &→0  ~&→1  |→1  ~|→0  ^→1  ~^→0
  MakeVar4(f, "v", 4, 0b1000, 0);
  auto id = [&]() { return MakeId(f.arena, "v"); };

  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kAmp, id()), f.ctx, f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeAmp, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            1u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kPipe, id()), f.ctx, f.arena)
          .ToUint64(),
      1u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildePipe, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(
      EvalExpr(MakeUnary(f.arena, TokenKind::kCaret, id()), f.ctx, f.arena)
          .ToUint64(),
      1u);
  EXPECT_EQ(EvalExpr(MakeUnary(f.arena, TokenKind::kTildeCaret, id()), f.ctx,
                     f.arena)
                .ToUint64(),
            0u);
}

}  // namespace
