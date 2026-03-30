#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/adv_sim.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(AssignmentWithinExpression, AssignInExprBasic) {
  SimFixture f;

  MakeVar(f, "aie", 32, 0);
  auto* assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie");
  assign->rhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(assign, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  auto* var = f.ctx.FindVariable("aie");
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentWithinExpression, AssignInExprTruncToLHSWidth) {
  SimFixture f;

  MakeVar(f, "aie8", 8, 0);
  auto* assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie8");
  assign->rhs = MakeInt(f.arena, 0x1FF);
  auto result = EvalExpr(assign, f.ctx, f.arena);

  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(AssignmentWithinExpression, CompoundAddAssignReturnsUpdatedValue) {
  SimFixture f;
  MakeVar(f, "x", 32, 10);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlusEq, MakeId(f.arena, "x"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 15u);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 15u);
}

TEST(AssignmentWithinExpression, CompoundSubAssignReturnsUpdatedValue) {
  SimFixture f;
  MakeVar(f, "x", 32, 10);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinusEq, MakeId(f.arena, "x"),
                          MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 7u);
}

TEST(AssignmentWithinExpression, CompoundMulAssignReturnsUpdatedValue) {
  SimFixture f;
  MakeVar(f, "x", 32, 6);
  auto* expr = MakeBinary(f.arena, TokenKind::kStarEq, MakeId(f.arena, "x"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 42u);
}

TEST(AssignmentWithinExpression, ChainedAssignUpdatesAllVariables) {
  SimFixture f;
  MakeVar(f, "a", 32, 0);
  MakeVar(f, "b", 32, 0);
  // a = (b = 5): inner assigns 5 to b, returns 5; outer assigns 5 to a.
  auto* inner = MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "b"),
                           MakeInt(f.arena, 5));
  auto* outer = MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "a"),
                           inner);
  auto result = EvalExpr(outer, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 5u);
}

TEST(AssignmentWithinExpression, ReturnValueMatchesLhsWidth) {
  SimFixture f;
  // LHS is 4-bit; assigning 0xFF should return a 4-bit value (0xF).
  MakeVar(f, "narrow", 4, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "narrow"),
                          MakeInt(f.arena, 0xFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
}

TEST(AssignmentWithinExpression, AssignInExprReturnUsedByOuterExpr) {
  SimFixture f;
  MakeVar(f, "a", 32, 0);
  // (a = 10) + 20 should return 30 and set a to 10.
  auto* assign = MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "a"),
                            MakeInt(f.arena, 10));
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, assign,
                         MakeInt(f.arena, 20));
  auto result = EvalExpr(add, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 30u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
}

}  // namespace
