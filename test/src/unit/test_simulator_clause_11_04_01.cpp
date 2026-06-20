#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LvalueSim, VarLvalueCompoundAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x += 5; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(CompoundAssignOpEval, PlusEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 15u);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(CompoundAssignOpEval, MinusEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 20);

  auto* expr = MakeBinary(f.arena, TokenKind::kMinusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 13u);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(CompoundAssignOpEval, StarEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 6);

  auto* expr = MakeBinary(f.arena, TokenKind::kStarEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CompoundAssignOpEval, SlashEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* expr = MakeBinary(f.arena, TokenKind::kSlashEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(CompoundAssignOpEval, PercentEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("m", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 17);

  auto* expr = MakeBinary(f.arena, TokenKind::kPercentEq, MakeId(f.arena, "m"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(CompoundAssignOpEval, LtLtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(CompoundAssignOpEval, GtGtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(LvalueSim, CompoundAssignWithIndexedLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    arr[2] += 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("arr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->unpacked_array[2].ToUint64(), 15u);
}

TEST(CompoundAssignOpEval, LtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(CompoundAssignOpEval, GtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(LvalueSim, CompoundAssignEvaluatesLvalueIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    arr[idx_fn()] += 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* arr = f.ctx.FindVariable("arr");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(arr, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(arr->unpacked_array[2].ToUint64(), 15u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

TEST(LvalueSim, CompoundAssignSelfReferenceDoublesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    a += a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LvalueSim, CompoundAssignArithBitwiseShiftThroughPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sub, mul, divr, mod;\n"
      "  int band, bor, bxor;\n"
      "  int shl, shr;\n"
      "  initial begin\n"
      "    sub = 10;  sub  -= 3;\n"
      "    mul = 6;   mul  *= 2;\n"
      "    divr = 8;  divr /= 2;\n"
      "    mod = 17;  mod  %= 5;\n"
      "    band = 'hFF; band &= 'h0F;\n"
      "    bor  = 'h01; bor  |= 'h10;\n"
      "    bxor = 'hAA; bxor ^= 'hFF;\n"
      "    shl = 1;   shl  <<= 4;\n"
      "    shr = 256; shr  >>= 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sub")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("mul")->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("divr")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("mod")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("band")->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(f.ctx.FindVariable("bor")->value.ToUint64(), 0x11u);
  EXPECT_EQ(f.ctx.FindVariable("bxor")->value.ToUint64(), 0x55u);
  EXPECT_EQ(f.ctx.FindVariable("shl")->value.ToUint64(), 16u);
  EXPECT_EQ(f.ctx.FindVariable("shr")->value.ToUint64(), 16u);
}

}  // namespace
