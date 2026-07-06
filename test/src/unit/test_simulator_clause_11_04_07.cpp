#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalOp, AmpEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeBinary(f.arena, TokenKind::kAmpEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(EvalOp, PipeEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xF0);

  auto* expr = MakeBinary(f.arena, TokenKind::kPipeEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(EvalOp, CaretEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeBinary(f.arena, TokenKind::kCaretEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xF0u);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(EvalOpXZ, LogicalNotZero) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalNotNonzero) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeInt(f.arena, 237));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalNotX) {
  SimFixture f;

  MakeVar4(f, "ln", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "ln"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndZeroX) {
  SimFixture f;

  MakeVar4(f, "lx", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 0),
                          MakeId(f.arena, "lx"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndXZero) {
  SimFixture f;

  MakeVar4(f, "ax", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "ax"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndXX) {
  SimFixture f;

  MakeVar4(f, "bx", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "bx"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrOneX) {
  SimFixture f;

  MakeVar4(f, "ox", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 1),
                          MakeId(f.arena, "ox"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrXOne) {
  SimFixture f;

  MakeVar4(f, "px", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "px"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrXX) {
  SimFixture f;

  MakeVar4(f, "qx", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "qx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ImplicationTrueTrue) {
  SimFixture f;

  MakeVar4(f, "it1", 1, 1, 0);
  MakeVar4(f, "it2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplicationTrueFalse) {
  SimFixture f;

  MakeVar4(f, "it1", 1, 1, 0);
  MakeVar4(f, "it2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, ImplicationFalseTrue) {
  SimFixture f;

  MakeVar4(f, "it1", 1, 0, 0);
  MakeVar4(f, "it2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplicationFalseFalse) {
  SimFixture f;

  MakeVar4(f, "it1", 1, 0, 0);
  MakeVar4(f, "it2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplicationUnknownTrue) {
  SimFixture f;

  MakeVar4(f, "ix1", 1, 0, 1);
  MakeVar4(f, "ix2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ix1"),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ImplicationUnknownFalse) {
  SimFixture f;

  MakeVar4(f, "ix1", 1, 0, 1);
  MakeVar4(f, "ix2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ix1"),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ImplicationFalseUnknown) {
  // A false antecedent makes the implication true regardless of the
  // consequent, so the result is a known 1 even when the consequent is x.
  SimFixture f;

  MakeVar4(f, "ifu1", 1, 0, 0);
  MakeVar4(f, "ifu2", 1, 0, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ifu1"),
                          MakeId(f.arena, "ifu2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, EquivalenceResultIsOneBit) {
  // The equivalence of two multibit operands reduces to a single-bit logical
  // result; both operands here are nonzero, so they compare equal.
  SimFixture f;

  MakeVar4(f, "erw1", 4, 0b1010, 0);
  MakeVar4(f, "erw2", 4, 0b0001, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt,
                          MakeId(f.arena, "erw1"), MakeId(f.arena, "erw2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, EquivalenceSameValue) {
  SimFixture f;

  MakeVar4(f, "eq1", 1, 1, 0);
  MakeVar4(f, "eq2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "eq1"),
                          MakeId(f.arena, "eq2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, EquivalenceDifferentValues) {
  SimFixture f;

  MakeVar4(f, "eq1", 1, 1, 0);
  MakeVar4(f, "eq2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "eq1"),
                          MakeId(f.arena, "eq2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, EquivalenceUnknownOperand) {
  SimFixture f;

  MakeVar4(f, "ex1", 1, 0, 1);
  MakeVar4(f, "ex2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "ex1"),
                          MakeId(f.arena, "ex2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndTrueTrue) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 1),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, LogicalAndTrueFalse) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 1),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, LogicalAndFalseTrue) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, LogicalAndFalseFalse) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, LogicalOrTrueTrue) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 1),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, LogicalOrTrueFalse) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 1),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, LogicalOrFalseTrue) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, LogicalOrFalseFalse) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, ImplicationTrueUnknown) {
  SimFixture f;
  MakeVar4(f, "ix2", 1, 0, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeInt(f.arena, 1),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, EquivalenceFalseFalse) {
  SimFixture f;
  MakeVar4(f, "e1", 1, 0, 0);
  MakeVar4(f, "e2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "e1"),
                          MakeId(f.arena, "e2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, EquivalenceFalseTrue) {
  SimFixture f;
  MakeVar4(f, "e1", 1, 0, 0);
  MakeVar4(f, "e2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "e1"),
                          MakeId(f.arena, "e2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(OperatorSim, ShortCircuitAndSkipsRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = (0 && (1/0));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(OperatorSim, ShortCircuitOrSkipsRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = (1 || (1/0));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(OperatorSim, ShortCircuitImplicationSkipsRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = (0 -> (1/0));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(OperatorSim, ShortCircuitAlwaysEvaluatesFirstOperand) {
  // Short-circuit evaluation still requires the first operand to be evaluated.
  // The first operand here has a side effect that must take place; the second
  // operand forces the && result to false without undoing that side effect.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, y;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    y = ((a = a + 1) && 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

TEST(OperatorSim, EquivalenceEvaluatesEachOperandOnce) {
  // The equivalence operator is defined in terms of two implications, but the
  // LRM requires each operand to be evaluated exactly once rather than once per
  // implication. Each operand here increments its own counter as a side effect;
  // a correct evaluation leaves both counters at 1.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, y;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "    y = ((a = a + 1) <-> (b = b + 1));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);
  EXPECT_EQ(b->value.ToUint64(), 1u);
  // Both operands are nonzero, so the operands compare equal and y is true.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnaryLogicalNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = !1'b0;\n"
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

TEST(OperatorSim, BinaryLogicalAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd1 && 8'd1);\n"
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

TEST(OperatorSim, BinaryLogicalOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd0 || 8'd1);\n"
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

TEST(OperatorSim, BinaryImplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (1'b0 -> 1'b0);\n"
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

TEST(OperatorSim, BinaryEquivalence) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (1'b1 <-> 1'b1);\n"
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

TEST(AlwaysCombBasicSim, AlwaysCombLogicalOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a && !b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AlwaysStarSim, AlwaysStarLogicalNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic y;\n"
      "  always @* y = !a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(BlockingAssignSim, BlockingAssignUnaryOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  int r_not, r_bang;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    r_not = !a;\n"
      "    r_bang = !5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_not = f.ctx.FindVariable("r_not");
  auto* r_bang = f.ctx.FindVariable("r_bang");
  ASSERT_NE(r_not, nullptr);
  ASSERT_NE(r_bang, nullptr);

  EXPECT_EQ(r_not->value.ToUint64(), 1u);

  EXPECT_EQ(r_bang->value.ToUint64(), 0u);
}

TEST(BlockingAssignSim, BlockingAssignUnaryLogicalNotAndMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, neg_result, not_result;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    neg_result = -a;\n"
      "    not_result = !a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* neg = f.ctx.FindVariable("neg_result");
  ASSERT_NE(neg, nullptr);

  auto neg5_32bit = static_cast<uint32_t>(-5);
  EXPECT_EQ(neg->value.ToUint64(), neg5_32bit);

  auto* notv = f.ctx.FindVariable("not_result");
  ASSERT_NE(notv, nullptr);

  EXPECT_EQ(notv->value.ToUint64(), 0u);
}

TEST(OperatorSim, LogicalAndOfRelationalAndEqualityOperands) {
  // Example 2 of 11.4.7: a logical-AND chain whose operands are a relational
  // comparison (11.4.4) and two inequality comparisons (11.4.5). The &&
  // operator consumes the 1-bit results of those comparisons; the run observes
  // that the combined result is true only when every operand comparison is
  // true. The second evaluation flips one operand (c) so that `b != c` becomes
  // false, forcing the whole AND to 0 and proving the operands actually drive
  // it.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, size, b, c, index, lastone;\n"
      "  logic y_all, y_one;\n"
      "  initial begin\n"
      "    a = 2; size = 5;\n"
      "    b = 3; c = 4;\n"
      "    index = 7; lastone = 9;\n"
      "    y_all = (a < size-1) && (b != c) && (index != lastone);\n"
      "    c = 3;\n"
      "    y_one = (a < size-1) && (b != c) && (index != lastone);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y_all = f.ctx.FindVariable("y_all");
  auto* y_one = f.ctx.FindVariable("y_one");
  ASSERT_NE(y_all, nullptr);
  ASSERT_NE(y_one, nullptr);
  EXPECT_EQ(y_all->value.ToUint64(), 1u);
  EXPECT_EQ(y_all->value.words[0].bval, 0u);
  EXPECT_EQ(y_one->value.ToUint64(), 0u);
  EXPECT_EQ(y_one->value.words[0].bval, 0u);
}

TEST(OperatorSim, UnaryLogicalNotRealOperand) {
  // 11.4.7: the unary logical negation admits a real operand. A nonzero real is
  // a true value (negated to 0) and a zero real is a false value (negated to
  // 1). The operands are declared `real` variables so the real data type flows
  // through the whole pipeline rather than an integral one.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r_nz, r_z;\n"
      "  logic y_nz, y_z;\n"
      "  initial begin\n"
      "    r_nz = 2.5;\n"
      "    r_z = 0.0;\n"
      "    y_nz = !r_nz;\n"
      "    y_z = !r_z;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y_nz = f.ctx.FindVariable("y_nz");
  auto* y_z = f.ctx.FindVariable("y_z");
  ASSERT_NE(y_nz, nullptr);
  ASSERT_NE(y_z, nullptr);
  EXPECT_EQ(y_nz->value.ToUint64(), 0u);
  EXPECT_EQ(y_z->value.ToUint64(), 1u);
}

TEST(OperatorSim, LogicalAndOrRealOperands) {
  // 11.4.7: the binary logical operators admit real operands, treating a
  // nonzero real as true and a zero real as false. Real variables supply the
  // operands so the real data type is exercised end-to-end for both && and ||.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real a, b;\n"
      "  logic y_and, y_or;\n"
      "  initial begin\n"
      "    a = 2.5;\n"
      "    b = 0.0;\n"
      "    y_and = a && b;\n"
      "    y_or = a || b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y_and = f.ctx.FindVariable("y_and");
  auto* y_or = f.ctx.FindVariable("y_or");
  ASSERT_NE(y_and, nullptr);
  ASSERT_NE(y_or, nullptr);
  EXPECT_EQ(y_and->value.ToUint64(), 0u);
  EXPECT_EQ(y_or->value.ToUint64(), 1u);
}

TEST(BlockingAssignSim, BlockingAssignLogicalOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int r_and, r_or;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    r_and = a && b;\n"
      "    r_or  = a || b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_and = f.ctx.FindVariable("r_and");
  auto* r_or = f.ctx.FindVariable("r_or");
  ASSERT_NE(r_and, nullptr);
  ASSERT_NE(r_or, nullptr);
  EXPECT_EQ(r_and->value.ToUint64(), 0u);
  EXPECT_EQ(r_or->value.ToUint64(), 1u);
}

}  // namespace
