#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ShortCircuit, LogicalAndShortCircuitsOnFalseLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 42);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ShortCircuit, LogicalAndEvaluatesRhsWhenLhsTrue) {
  SimFixture f;
  MakeVar(f, "a", 8, 1);
  MakeVar(f, "b", 8, 1);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ShortCircuit, LogicalOrShortCircuitsOnTrueLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 5);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ShortCircuit, LogicalOrEvaluatesRhsWhenLhsFalse) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ShortCircuit, ImplicationShortCircuitsOnFalseLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 99);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kArrow,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ShortCircuit, BitwiseAndAlwaysEvaluatesBothOperands) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0xFF);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Helper: build an assignment-in-expression (side = val), usable as an operand.
inline Expr* MakeAssignExpr(Arena& arena, const char* name, uint64_t val) {
  return MakeBinary(arena, TokenKind::kEq, MakeId(arena, name),
                    MakeInt(arena, val));
}

// Side-effect tests: verify short-circuited operands are truly not evaluated.

TEST(ShortCircuit, LogicalAndFalseLhsSkipsRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "se", 8, 99);
  auto result = EvalExpr(
      MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "a"),
                 MakeAssignExpr(f.arena, "se", 42)),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 99u);
}

TEST(ShortCircuit, LogicalAndTrueLhsExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 1);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

TEST(ShortCircuit, LogicalOrTrueLhsSkipsRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 1);
  MakeVar(f, "se", 8, 99);
  auto result = EvalExpr(
      MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "a"),
                 MakeAssignExpr(f.arena, "se", 42)),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 99u);
}

TEST(ShortCircuit, LogicalOrFalseLhsExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

TEST(ShortCircuit, ImplicationFalseLhsSkipsRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "se", 8, 99);
  auto result = EvalExpr(
      MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "a"),
                 MakeAssignExpr(f.arena, "se", 42)),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 99u);
}

TEST(ShortCircuit, ImplicationTrueLhsExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 1);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

// Non-short-circuit operators: verify both operands are always evaluated.

TEST(ShortCircuit, BitwiseOrAlwaysExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xFF);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kPipe, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

TEST(ShortCircuit, AdditionAlwaysExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

TEST(ShortCircuit, MultiplyAlwaysExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

TEST(ShortCircuit, EqualityAlwaysExecutesRhsSideEffect) {
  SimFixture f;
  MakeVar(f, "a", 8, 5);
  MakeVar(f, "se", 8, 99);
  EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "a"),
                      MakeAssignExpr(f.arena, "se", 42)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 42u);
}

}  // namespace
