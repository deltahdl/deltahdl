#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ExpressionSim, PrefixIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PrefixDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; --x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x++; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(LvalueSim, VarLvaluePreIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(LvalueSim, VarLvaluePostDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PrefixIncReturnsNewValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin x = 5; y = ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixIncReturnsOldValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin x = 5; y = x++; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 5u);
}

TEST(ExpressionSim, PrefixDecReturnsNewValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin x = 10; y = --x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 9u);
  EXPECT_EQ(vy->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixDecReturnsOldValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin x = 10; y = x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 9u);
  EXPECT_EQ(vy->value.ToUint64(), 10u);
}

static double AdvToDouble(const Logic4Vec& v) {
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

static Variable* MakeRealVarAdv(SimFixture& f, std::string_view name,
                                double val) {
  auto* var = f.ctx.CreateVariable(name, 64);
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  var->value = MakeLogic4VecVal(f.arena, 64, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}

TEST(RealIncDecSim, PrefixIncrementBy1Point0) {
  SimFixture f;

  MakeRealVarAdv(f, "rv", 2.5);
  auto* inc = f.arena.Create<Expr>();
  inc->kind = ExprKind::kUnary;
  inc->op = TokenKind::kPlusPlus;
  inc->lhs = MakeId(f.arena, "rv");
  auto result = EvalExpr(inc, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(AdvToDouble(result), 3.5);
}

TEST(RealIncDecSim, PrefixDecrementBy1Point0) {
  SimFixture f;

  MakeRealVarAdv(f, "rv", 2.5);
  auto* dec = f.arena.Create<Expr>();
  dec->kind = ExprKind::kUnary;
  dec->op = TokenKind::kMinusMinus;
  dec->lhs = MakeId(f.arena, "rv");
  auto result = EvalExpr(dec, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(AdvToDouble(result), 1.5);
}

TEST(RealIncDecSim, PostfixIncrementBy1Point0) {
  SimFixture f;

  MakeRealVarAdv(f, "rv", 4.0);
  auto* inc = f.arena.Create<Expr>();
  inc->kind = ExprKind::kPostfixUnary;
  inc->op = TokenKind::kPlusPlus;
  inc->lhs = MakeId(f.arena, "rv");
  auto result = EvalPostfixUnary(inc, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(AdvToDouble(result), 4.0);
  auto* var = f.ctx.FindVariable("rv");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(AdvToDouble(var->value), 5.0);
}

TEST(RealIncDecSim, PostfixDecrementBy1Point0) {
  SimFixture f;

  MakeRealVarAdv(f, "rv", 4.0);
  auto* dec = f.arena.Create<Expr>();
  dec->kind = ExprKind::kPostfixUnary;
  dec->op = TokenKind::kMinusMinus;
  dec->lhs = MakeId(f.arena, "rv");
  auto result = EvalPostfixUnary(dec, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(AdvToDouble(result), 4.0);
  auto* var = f.ctx.FindVariable("rv");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(AdvToDouble(var->value), 3.0);
}

}  // namespace
