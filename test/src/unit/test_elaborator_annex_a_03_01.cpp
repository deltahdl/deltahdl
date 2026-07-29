#include "fixture_elaborator.h"
#include "helpers_ninput_gate_elab.h"

using namespace delta;

namespace {

TEST(GateElaboration, AndGateProducesContAssign) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("and"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(GateElaboration, NandGateProducesInvertedAnd) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("nand"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(GateElaboration, OrGateProducesContAssign) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("or"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

TEST(GateElaboration, NorGateProducesInvertedOr) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("nor"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
}

TEST(GateElaboration, XorGateProducesContAssign) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("xor"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

TEST(GateElaboration, XnorGateProducesInvertedXor) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("xnor"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
}

TEST(GateElaboration, NInputThreeInputsProducesBinaryChain) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(
      "module m;\n"
      "  wire a, b, c, y;\n"
      "  and g1(y, a, b, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
}

// A.3.1 gate_instantiation: a buf instance elaborates into a continuous
// assignment driving its output from its input. The driving expression is not
// the bare input, because Table 28-4 gives buf the mapping 0->0, 1->1, x->x and
// z->x: buf is a non-tristate driver, so a high-impedance input emerges as
// unknown rather than passing through. Handing the identifier straight to the
// output would propagate the z. A complement already folds z to x, so the
// value-preserving form of that fold is a pair of them -- which is what tells
// buf's assignment apart from the single complement not gets below.
TEST(GateElaboration, BufGateProducesContAssign) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(
      "module m;\n"
      "  wire a, y;\n"
      "  buf g1(y, a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kIdentifier);
}

TEST(GateElaboration, NotGateProducesInvertedAssign) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(
      "module m;\n"
      "  wire a, y;\n"
      "  not g1(y, a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

TEST(GateElaboration, MultipleGatesProduceMultipleAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y1, y2;\n"
      "  and g1(y1, a, b);\n"
      "  or  g2(y2, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 2u);
}

}  // namespace
