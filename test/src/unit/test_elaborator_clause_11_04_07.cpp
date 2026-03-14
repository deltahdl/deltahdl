#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ConstEval, Logical) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 0", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 0", f)), 0);
}

TEST(ConstEval, Unary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("-5", f)), -5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!0", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!5", f)), 0);
}

TEST(OperatorElaboration, UnaryLogicalNotElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x, a;\n"
      "  initial x = !a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryImplicationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (1'b0 -> 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryEquivalenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (1'b1 <-> 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
