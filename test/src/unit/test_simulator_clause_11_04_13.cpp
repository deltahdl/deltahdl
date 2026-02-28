// §11.4.13: for an explanation of range list syntax.

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/adv_sim.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

static Expr* MakeRange(Arena& arena, Expr* lo, Expr* hi,
                       TokenKind op = TokenKind::kEof) {
  auto* r = arena.Create<Expr>();
  r->kind = ExprKind::kSelect;
  r->index = lo;
  r->index_end = hi;
  r->op = op;
  return r;
}

namespace {

TEST(EvalAdv, InsideAbsTolerance) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("at", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "at");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideAbsToleranceMiss) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("am", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 20);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "am");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, InsideRelTolerance) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("rt", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 8);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "rt");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 10),
                                       MakeInt(f.arena, 25),
                                       TokenKind::kPlusPercentMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// ==========================================================================
// Inside operator X/Z — §11.4.13
// ==========================================================================
TEST(EvalOpXZ, InsideXOperand) {
  SimFixture f;
  // x inside {3, 5, 7} → x (unknown operand, no definite match)
  MakeVar4(f, "ix", 4, 0b0000, 0b0100);  // 4'b0x00

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ix");
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// § inside_expression — value match
TEST(SimA83, InsideValueMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd5 inside {8'd3, 8'd5, 8'd7};\n"
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
