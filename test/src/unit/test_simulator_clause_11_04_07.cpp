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
