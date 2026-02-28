// §11.4.11: Conditional operator

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_eval_op.h"

using namespace delta;

namespace {

// ==========================================================================
// Ternary X/Z condition — §11.4.11
// ==========================================================================
TEST(EvalOpXZ, TernaryZCond) {
  SimFixture f;
  // z ? 4'b1100 : 4'b1010 → same as x condition (bit-by-bit combine)
  MakeVar4(f, "tz", 1, 0, 1);  // 1'bz (aval=0, bval=1)
  auto* tv = f.ctx.CreateVariable("zt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("zf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tz");
  ternary->true_expr = MakeId(f.arena, "zt");
  ternary->false_expr = MakeId(f.arena, "zf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  // Same as TernaryXCondDiff: aval=0b1000, bval=0b0110
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

TEST(EvalOpXZ, TernaryXCondSame) {
  SimFixture f;
  // x ? 5 : 5 → 5 (both branches same → known result)
  MakeVar4(f, "tc", 1, 0, 1);  // 1'bx
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tc");
  ternary->true_expr = MakeInt(f.arena, 5);
  ternary->false_expr = MakeInt(f.arena, 5);
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, TernaryXCondDiff) {
  SimFixture f;
  // x ? 4'b1100 : 4'b1010 → 4'b1x0x (matching bits kept, differing → X)
  MakeVar4(f, "td", 1, 0, 1);  // 1'bx
  auto* tv = f.ctx.CreateVariable("tt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("tf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "td");
  ternary->true_expr = MakeId(f.arena, "tt");
  ternary->false_expr = MakeId(f.arena, "tf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  // 4'b1x0x: bits that match keep value, bits that differ → X
  //   bit3: 1==1 → 1 (aval=1, bval=0)
  //   bit2: 1!=0 → x (aval=0, bval=1)
  //   bit1: 0!=1 → x (aval=0, bval=1)
  //   bit0: 0==0 → 0 (aval=0, bval=0)
  // aval=0b1000, bval=0b0110
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

// § conditional_expression — ternary true branch
TEST(SimA83, TernaryTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd10 : 8'd20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// § conditional_expression — ternary false branch
TEST(SimA83, TernaryFalseBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 0 ? 8'd10 : 8'd20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// § conditional_expression — nested ternary
TEST(SimA83, NestedTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? (0 ? 8'd1 : 8'd2) : 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
