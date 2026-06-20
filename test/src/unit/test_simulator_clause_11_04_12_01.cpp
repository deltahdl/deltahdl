#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Builds a replication of a side-effecting post-increment operand on a fresh
// 8-bit variable "i" (initialized to 0) with the given multiplier, evaluates
// it, and returns the result. The post-increment lets callers observe that the
// operand is evaluated exactly once regardless of the multiplier.
Logic4Vec EvalPostIncReplication(SimFixture& f, uint64_t repeat_count) {
  auto* counter = f.ctx.CreateVariable("i", 8);
  counter->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* inc = f.arena.Create<Expr>();
  inc->kind = ExprKind::kPostfixUnary;
  inc->op = TokenKind::kPlusPlus;
  inc->lhs = MakeId(f.arena, "i");

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, repeat_count);
  rep->elements.push_back(inc);

  return EvalExpr(rep, f.ctx, f.arena);
}

TEST(ReplicationSim, ReplicationBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {2{4'hA}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(ReplicationSim, ReplicationFourCopies) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {4{2'b10}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(ReplicationSim, ReplicationMultipleInner) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = {2{4'hA, 4'h5}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xA5A5u);
}

TEST(ReplicationEval, ReplicationSingleCopy) {
  SimFixture f;

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 1);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(ReplicationEval, ReplicationXZPropagation) {
  SimFixture f;

  MakeVar4(f, "rv", 4, 0b1001, 0b0101);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 2);
  rep->elements.push_back(MakeId(f.arena, "rv"));

  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x99u);
  EXPECT_EQ(result.words[0].bval, 0x55u);
}

TEST(ReplicationSim, ReplicationNestedInConcatValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [27:0] result;\n"
      "  initial begin\n"
      "    a = 4'h1;\n"
      "    b = 4'h2;\n"
      "    result = {b, {3{a, b}}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2121212u);
}

TEST(ReplicationEval, ReplicationWidthIsCountTimesInnerWidth) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("v", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0xA);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 5);
  rep->elements.push_back(MakeId(f.arena, "v"));
  auto result = EvalExpr(rep, f.ctx, f.arena);

  EXPECT_EQ(result.width, 20u);
  EXPECT_EQ(result.ToUint64(), 0xAAAAAu);
}

TEST(ReplicationEval, ZeroReplicationWidth) {
  SimFixture f;

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 0);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);

  EXPECT_EQ(result.width, 0u);
}

// §11.4.12.1: a zero-multiplier replication has size zero and is ignored, so
// inside a concatenation it contributes no bits and the result equals the
// positive-size operand alone.
TEST(ReplicationSim, ZeroReplicationIgnoredInConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'hF;\n"
      "    result = {a, {0{b}}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// §11.4.12.1: the operands of a replication are evaluated exactly once,
// regardless of how many copies the multiplier requests. A side-effecting
// operand (post-increment) lets us observe the evaluation count: the
// variable advances by exactly one even though four copies are produced.
TEST(ReplicationEval, OperandsEvaluatedOnce) {
  SimFixture f;

  EvalPostIncReplication(f, 4);

  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 1u);
}

// §11.4.12.1: a zero multiplier still evaluates the operands exactly once,
// even though the replication itself contributes no bits.
TEST(ReplicationEval, OperandsEvaluatedOnceWithZeroMultiplier) {
  SimFixture f;

  auto result = EvalPostIncReplication(f, 0);

  EXPECT_EQ(result.width, 0u);
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 1u);
}

}  // namespace
