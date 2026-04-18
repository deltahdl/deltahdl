#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(NInputGateElaboration, ElaborateAndGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];

  ASSERT_GE(mod->assigns.size(), 1);
  auto& ca = mod->assigns[0];
  EXPECT_NE(ca.lhs, nullptr);
  EXPECT_NE(ca.rhs, nullptr);

  EXPECT_EQ(ca.rhs->op, TokenKind::kAmp);
}

TEST(NInputGateElaboration, ElaborateNandGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  nand g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);

  auto* rhs = mod->assigns[0].rhs;
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  EXPECT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(NInputGateElaboration, ElaborateXorGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  xor g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kCaret);
}

// --- N-input gate chain depth ---
TEST(NInputGateElaboration, FourInputAndProducesThreeNodeChain) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, c, d, y;\n"
      "  and g1(y, a, b, c, d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  // (a & b) & c) & d => root is binary, lhs is binary, lhs->lhs is binary
  ASSERT_NE(ca.rhs->lhs, nullptr);
  EXPECT_EQ(ca.rhs->lhs->kind, ExprKind::kBinary);
  ASSERT_NE(ca.rhs->lhs->lhs, nullptr);
  EXPECT_EQ(ca.rhs->lhs->lhs->kind, ExprKind::kBinary);
}

TEST(NInputGateElaboration, TwoInputOrProducesSingleBinary) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  or g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kPipe);
  EXPECT_EQ(ca.rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca.rhs->rhs->kind, ExprKind::kIdentifier);
}

// --- Full pipeline: elaborate through preprocessor ---
TEST(NInputGateElaboration, NandGateElaboratesThroughFullPipeline) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endmodule\n"));
}

// nor and xnor complete the six n-input gates; each inverts its base gate's
// binary-chain expression.
TEST(NInputGateElaboration, ElaborateNorGate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nor g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
}

TEST(NInputGateElaboration, ElaborateXnorGate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xnor g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
}

// The first terminal drives the output, so the elaborated continuous
// assignment must use it as the lhs.
TEST(NInputGateElaboration, FirstTerminalIsOutputLhs) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* lhs = mod->assigns[0].lhs;
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(lhs->text, "y");
}

}  // namespace
