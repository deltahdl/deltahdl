#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

static Variable* MakeVar4Adv(SimFixture& f, std::string_view name,
                             uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}
namespace {

TEST(EvalAdv, ComparisonResultUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "ca", 8, 1);
  MakeSignedVarAdv(f, "cb", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ca"),
                          MakeId(f.arena, "cb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, ReductionResultUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "rv", 8, 0xFF);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, ConcatResultUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "c1", 4, 0xA);
  MakeSignedVarAdv(f, "c2", 4, 0xB);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "c1"));
  concat->elements.push_back(MakeId(f.arena, "c2"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, BitwiseSignedResult) {
  SimFixture f;
  MakeSignedVarAdv(f, "b1", 8, 0xFF);
  MakeSignedVarAdv(f, "b2", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "b1"),
                          MakeId(f.arena, "b2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, MixedSignUnsignedResult) {
  SimFixture f;
  MakeSignedVarAdv(f, "ms", 8, 0xFF);
  auto* u = MakeVar(f, "mu", 8, 0x0F);
  (void)u;
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ms"),
                          MakeId(f.arena, "mu"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, BitSelectUnsigned) {
  SimFixture f;

  MakeSignedVarAdv(f, "bs", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bs");
  sel->index = MakeInt(f.arena, 3);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, PartSelectUnsigned) {
  SimFixture f;

  MakeSignedVarAdv(f, "ps", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ps");
  sel->index = MakeInt(f.arena, 0);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, SignedXFillsX) {
  SimFixture f;

  auto* var = MakeVar4Adv(f, "sx", 4, 0b0001, 0b1000);
  var->is_signed = true;

  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);

  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

TEST(EvalAdv, SignedZFillsZ) {
  SimFixture f;

  auto* var = MakeVar4Adv(f, "sz", 4, 0b0001, 0b1000);
  var->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sz"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);

  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

TEST(SignedExprSim, SystemTfCallUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = $unsigned(8'sd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(SignedExprSim, UnsignedPreservesValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SignedExprSim, SignedPreservesValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SignedExprSim, SignedSetsSignedFlag) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xAB);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "a")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, UnsignedClearsSignedFlag) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 0xAB);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "a")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, SignedPreservesWidth) {
  SimFixture f;
  MakeVar(f, "w", 16, 0x1234);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "w")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x1234u);
}

TEST(SignedExprSim, UnsignedPreservesWidth) {
  SimFixture f;
  MakeSignedVarAdv(f, "w", 16, 0x1234);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "w")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x1234u);
}

TEST(SignedExprSim, SignedOnAlreadySignedIsNoop) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0xFF);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "s")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, UnsignedOnAlreadyUnsignedIsNoop) {
  SimFixture f;
  MakeVar(f, "u", 8, 0xFF);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "u")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, SignedPreservesBitPattern) {
  SimFixture f;
  MakeVar(f, "v", 8, 0b11001010);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b11001010u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedExprSim, UnsignedPreservesBitPattern) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0b11001010);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b11001010u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedExprSim, EmptyArgsReturnsZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SignedExprSim, LrmExampleUnsignedNeg4) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] regA;\n"
      "  initial regA = $unsigned(-4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("regA");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, LrmExampleSignedBitLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] regS;\n"
      "  initial regS = $signed(4'b1100);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, SignedAdditionEndToEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] regA, regB;\n"
      "  logic signed [7:0] regS;\n"
      "  initial begin\n"
      "    regA = 8'hFF;\n"
      "    regB = 8'h01;\n"
      "    regS = $signed(regA) + $signed(regB);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SignedExprSim, SystemTfCallSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  initial x = $signed(8'd200);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

}  // namespace
