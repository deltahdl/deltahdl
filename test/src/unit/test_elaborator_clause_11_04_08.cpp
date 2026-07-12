#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstEval, Bitwise) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 & 10", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 | 3", f)), 15);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 ^ 3", f)), 6);
}

TEST(ConstEval, BitwiseXnor) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("8'hFF ^~ 8'h0F", f)), 0x0F);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("4'b1100 ~^ 4'b1010", f)), 0b1001);
}

TEST(ConstEval, BitwiseNot) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("~8'hF0", f)), 0x0F);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("~8'h00", f)), 0xFF);
}

TEST(OperatorElaboration, UnaryBitwiseNotElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryBitwiseXnorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF ^~ 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombBasicSim, AlwaysCombBitwiseAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(AlwaysCombExtendedSim, AlwaysCombNand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = ~(a & b);\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h0F;\n"
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

  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0xF0u);
}

TEST(AlwaysCombExtendedSim, AlwaysCombChainedBitwise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, y;\n"
      "  always_comb y = (a ^ b) | c;\n"
      "  initial begin\n"
      "    a = 8'hA0;\n"
      "    b = 8'h50;\n"
      "    c = 8'h0F;\n"
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

  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

TEST(BlockingAssignSim, BlockingAssignBitwiseOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int r_and, r_or, r_xor;\n"
      "  initial begin\n"
      "    a = 240;\n"
      "    b = 60;\n"
      "    r_and = a & b;\n"
      "    r_or  = a | b;\n"
      "    r_xor = a ^ b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r_and", 48u}, {"r_or", 252u}, {"r_xor", 204u}});
}

// §11.4.8 binary bitwise AND folded in a constant expression whose operand is a
// `parameter`. A parameter reference resolves through the identifier path in
// the constant evaluator, distinct from the literal path exercised by ConstEval
// above, so the same bit-by-bit AND is observed on a differently produced
// operand: 12 & 10 folds to 8.
TEST(ConstEval, BinaryBitwiseAndOfParameterFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 12;\n"
      "  localparam Q = P & 10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& q = design->top_modules[0]->params[1];
  EXPECT_EQ(q.name, "Q");
  EXPECT_EQ(q.resolved_value, 8);
}

// §11.4.8 binary bitwise OR folded with a `localparam` operand, which likewise
// takes the identifier-resolution path: 12 | 3 folds to 15.
TEST(ConstEval, BinaryBitwiseOrOfLocalparamFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam A = 12;\n"
      "  localparam B = A | 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_EQ(b.resolved_value, 15);
}

// §11.4.8 binary bitwise XOR folded with a `parameter` operand: 5 ^ 3 folds to
// 6.
TEST(ConstEval, BinaryBitwiseXorOfParameterFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 5;\n"
      "  localparam Q = P ^ 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& q = design->top_modules[0]->params[1];
  EXPECT_EQ(q.name, "Q");
  EXPECT_EQ(q.resolved_value, 6);
}

// §11.4.8 binary bitwise XNOR (^~) folded with a `localparam` operand. XNOR is
// the negated XOR: over the low 8 bits, 8'hFF ~^ 8'h0F yields ~(8'hF0) = 8'h0F.
// The result is masked to the declared width so the check is independent of the
// fold's internal carrier width.
TEST(ConstEval, BinaryBitwiseXnorOfLocalparamFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [7:0] A = 8'hFF;\n"
      "  localparam [7:0] B = A ~^ 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_EQ(b.resolved_value & 0xFF, 0x0F);
}

// §11.4.8 unary bitwise negation folded with a `parameter` operand, driving the
// per-bit negation on an identifier-resolved constant rather than a literal:
// over the low 8 bits, ~8'h0F yields 8'hF0.
TEST(ConstEval, UnaryBitwiseNotOfParameterFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [7:0] P = 8'h0F;\n"
      "  localparam [7:0] Q = ~P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& q = design->top_modules[0]->params[1];
  EXPECT_EQ(q.name, "Q");
  EXPECT_EQ(q.resolved_value & 0xFF, 0xF0);
}

}  // namespace
