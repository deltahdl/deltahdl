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

TEST(EvalOp, PlusEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 15u);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(EvalOp, MinusEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 20);

  auto* expr = MakeBinary(f.arena, TokenKind::kMinusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 13u);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(EvalOp, StarEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 6);

  auto* expr = MakeBinary(f.arena, TokenKind::kStarEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EvalOp, SlashEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* expr = MakeBinary(f.arena, TokenKind::kSlashEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(EvalOp, PercentEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("m", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 17);

  auto* expr = MakeBinary(f.arena, TokenKind::kPercentEq, MakeId(f.arena, "m"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EvalOp, LtLtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(EvalOp, GtGtGtEq) {
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

}  // namespace
