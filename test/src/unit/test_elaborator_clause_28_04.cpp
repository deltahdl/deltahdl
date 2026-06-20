#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_ninput_gate_elab.h"
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

TEST(NInputGateElaboration, FourInputAndProducesThreeNodeChain) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(
      "module m;\n"
      "  wire a, b, c, d, y;\n"
      "  and g1(y, a, b, c, d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);

  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kBinary);
}

TEST(NInputGateElaboration, TwoInputOrProducesSingleBinary) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(TwoInputGateSrc("or"), f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(NInputGateElaboration, ElaborateNorGate) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(
      "module m;\n"
      "  wire y, a, b;\n"
      "  nor g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
}

TEST(NInputGateElaboration, ElaborateXnorGate) {
  ElabFixture f;
  auto* rhs = ElaborateNInputGateRhs(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xnor g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
}

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

TEST(NInputGateElaboration, PropagationDelayIndependentOfInputCount) {
  // For each input arity, the elaborator emits one continuous assign carrying
  // the same #(7) delay; adding more inputs only widens the AND chain.
  const char* kSources[] = {
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #(7) g(y, a, b);\n"
      "endmodule\n",
      "module m;\n"
      "  wire y, a, b, c;\n"
      "  and #(7) g(y, a, b, c);\n"
      "endmodule\n",
      "module m;\n"
      "  wire y, a, b, c, d;\n"
      "  and #(7) g(y, a, b, c, d);\n"
      "endmodule\n",
      "module m;\n"
      "  wire y, a, b, c, d, e, f, g0, h;\n"
      "  and #(7) g(y, a, b, c, d, e, f, g0, h);\n"
      "endmodule\n",
  };
  for (const char* src : kSources) {
    ElabFixture f;
    auto* design = ElaborateSrc(src, f);
    ASSERT_NE(design, nullptr) << src;
    EXPECT_FALSE(f.has_errors) << src;
    auto* mod = design->top_modules[0];
    ASSERT_FALSE(mod->assigns.empty()) << src;
    auto& ca = mod->assigns[0];
    ASSERT_NE(ca.delay, nullptr) << src;
    EXPECT_EQ(ca.delay->int_val, 7u) << src;
    EXPECT_EQ(ca.delay_fall, nullptr) << src;
    EXPECT_EQ(ca.delay_decay, nullptr) << src;
  }
}

}  // namespace
