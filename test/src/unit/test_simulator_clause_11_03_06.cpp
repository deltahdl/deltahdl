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

  auto* inner = MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "b"),
                           MakeInt(f.arena, 5));
  auto* outer =
      MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "a"), inner);
  auto result = EvalExpr(outer, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 5u);
}

TEST(AssignmentWithinExpression, ReturnValueMatchesLhsWidth) {
  SimFixture f;

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

  auto* assign = MakeBinary(f.arena, TokenKind::kEq, MakeId(f.arena, "a"),
                            MakeInt(f.arena, 10));
  auto* add =
      MakeBinary(f.arena, TokenKind::kPlus, assign, MakeInt(f.arena, 20));
  auto result = EvalExpr(add, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 30u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
}

// §11.3.6: when the target of an assignment within an expression is a
// concatenation, the returned value is an unsigned integral whose bit length
// is the sum of the operand lengths.
TEST(AssignmentWithinExpression, ConcatLhsReturnsUnsignedSumOfOperandWidths) {
  SimFixture f;
  MakeVar(f, "hi", 8, 0);
  MakeVar(f, "lo", 8, 0);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "hi"));
  concat->elements.push_back(MakeId(f.arena, "lo"));

  // A wider right-hand side is cast to the 16-bit concatenation target.
  auto* assign =
      MakeBinary(f.arena, TokenKind::kEq, concat, MakeInt(f.arena, 0x1ABCD));
  auto result = EvalExpr(assign, f.ctx, f.arena);

  EXPECT_EQ(result.width, 16u);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
  EXPECT_EQ(f.ctx.FindVariable("hi")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("lo")->value.ToUint64(), 0xCDu);
}

// §11.3.6: the concatenation result is unsigned even when the right-hand side
// already has the concatenation width and is itself signed.
TEST(AssignmentWithinExpression, ConcatLhsResultIsUnsignedForSignedRhs) {
  SimFixture f;
  MakeVar(f, "hi", 8, 0);
  MakeVar(f, "lo", 8, 0);
  // A signed source whose width equals the 16-bit concatenation target.
  MakeSignedVarAdv(f, "src", 16, 0xABCD);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "hi"));
  concat->elements.push_back(MakeId(f.arena, "lo"));

  auto* assign =
      MakeBinary(f.arena, TokenKind::kEq, concat, MakeId(f.arena, "src"));
  auto result = EvalExpr(assign, f.ctx, f.arena);

  EXPECT_EQ(result.width, 16u);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

}  // namespace
