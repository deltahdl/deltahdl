#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

// §11.4.12.1: the multiplier is a constant expression. This exercises the
// parameter form (§11.2.1) that the clause's own example uses — a localparam
// drives the copy count — and observes through the full pipeline that the
// elaborated constant produces exactly that many copies (three 4'hA nibbles).
TEST(ReplicationSim, LocalparamMultiplierCopyCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam N = 3;\n"
      "  logic [11:0] result;\n"
      "  initial result = {N{4'hA}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
  EXPECT_EQ(var->value.ToUint64(), 0xAAAu);
}

// §11.4.12.1: the multiplier is a constant expression. A module `parameter`
// (§11.2.1) is a distinct constant form from a localparam and takes its own
// declaration/override path; this drives one as the copy count through the
// full pipeline and observes three copies of 4'hA (0xAAA).
TEST(ReplicationSim, ParameterMultiplierCopyCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter N = 3;\n"
      "  logic [11:0] result;\n"
      "  initial result = {N{4'hA}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
  EXPECT_EQ(var->value.ToUint64(), 0xAAAu);
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

// §11.4.12.1: a zero multiplier yields size zero and is ignored inside a
// concatenation — the same rule the clause frames as useful in parameterized
// code. Here the zero comes from a `parameter` (§11.2.1) evaluated at
// elaboration rather than a literal, exercising the constant-fold path, and
// the run confirms the result is the positive-size operand alone (0xA5).
TEST(ReplicationSim, ParameterZeroMultiplierIgnoredInConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 0;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    b = 8'hFF;\n"
      "    result = {a, {P{b}}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// §11.4.12.1: the operands of a replication are evaluated exactly once,
// regardless of how many copies the multiplier requests. Driving a
// side-effecting operand (post-increment) through the full pipeline lets us
// observe the count from real source: i advances by exactly one, and the four
// copies all carry the single pre-increment value 5 (0x05050505) rather than
// the 5,6,7,8 sequence a per-copy re-evaluation would produce.
TEST(ReplicationSim, OperandsEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] i;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    i = 8'd5;\n"
      "    result = {4{i++}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 0x05050505u);
}

// §11.4.12.1: a zero multiplier still evaluates its operand exactly once even
// though the replication contributes no bits. Placed inside a concatenation
// with a positive-size operand (so the zero replication is legal), the
// post-increment fires once (i advances to 6) and the result equals the
// positive operand alone (0xA5).
TEST(ReplicationSim, OperandsEvaluatedOnceWithZeroMultiplier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] i;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    i = 8'd5;\n"
      "    a = 8'hA5;\n"
      "    result = {a, {0{i++}}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 0xA5u);
}

}  // namespace
