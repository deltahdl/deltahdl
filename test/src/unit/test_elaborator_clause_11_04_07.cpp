// §11.4.7: Logical operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

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

TEST(ElabA86, UnaryLogicalNotElaborates) {
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

// § binary_operator — implication operators elaborate
TEST(ElabA86, BinaryImplicationElaborates) {
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

TEST(ElabA86, BinaryEquivalenceElaborates) {
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

// ---------------------------------------------------------------------------
// 25. always_comb with logical operators.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombLogicalOps) {
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

// ---------------------------------------------------------------------------
// 30. always @* with logical NOT (!) on a multi-bit signal.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLogicalNot) {
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
  // !0 = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 15. Blocking assignment with unary operators (~, !).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignUnaryOps) {
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
  // !0 = 1
  EXPECT_EQ(r_not->value.ToUint64(), 1u);
  // !5 = 0
  EXPECT_EQ(r_bang->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 16. Blocking assignment with unary logical NOT (!) and unary minus (-).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignUnaryLogicalNotAndMinus) {
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
  // -5 as 32-bit unsigned = 0xFFFFFFFB
  auto neg5_32bit = static_cast<uint32_t>(-5);
  EXPECT_EQ(neg->value.ToUint64(), neg5_32bit);

  auto* notv = f.ctx.FindVariable("not_result");
  ASSERT_NE(notv, nullptr);
  // !5 = 0
  EXPECT_EQ(notv->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 21. Blocking assignment with logical operators (&&, ||).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignLogicalOps) {
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
  EXPECT_EQ(r_and->value.ToUint64(), 0u);  // 1 && 0 = 0
  EXPECT_EQ(r_or->value.ToUint64(), 1u);   // 1 || 0 = 1
}

}  // namespace
