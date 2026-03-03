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

}  // namespace
