#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Gate types not covered by subsection elaborator tests ---

TEST(GateElaboration, EnableGateProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif0 b1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& ca : mod->assigns) {
    EXPECT_NE(ca.lhs, nullptr);
  }
}

TEST(GateElaboration, MosSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, ctrl;\n"
      "  nmos n1(out, data, ctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateElaboration, CmosSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateElaboration, PassSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateElaboration, PassEnableSwitchProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- N-input gate chain depth ---

TEST(GateElaboration, FourInputAndProducesThreeNodeChain) {
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

TEST(GateElaboration, TwoInputOrProducesSingleBinary) {
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

// --- Gate with strength elaborates normally ---

TEST(GateElaboration, GateWithStrengthStillProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kAmp);
}

// --- Gate with delay elaborates normally ---

TEST(GateElaboration, GateWithDelayStillProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  or #10 g1(y, a, b);\n"
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
}

// --- Unnamed gate elaborates the same as named ---

TEST(GateElaboration, UnnamedGateProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  xor (y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kCaret);
}

// --- Full pipeline: elaborate through preprocessor ---

TEST(GateElaboration, GateThroughFullPipeline) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endmodule\n"));
}

TEST(GateElaboration, AllElaborableGatesThroughFullPipeline) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  wire a, b, c, y1, y2, y3, y4, y5, y6, o1, o2, n1, n2;\n"
      "  and (y1, a, b);\n"
      "  nand (y2, a, b);\n"
      "  or (y3, a, b);\n"
      "  nor (y4, a, b);\n"
      "  xor (y5, a, b);\n"
      "  xnor (y6, a, b);\n"
      "  buf (o1, a);\n"
      "  not (o2, a);\n"
      "  pullup (n1);\n"
      "  pulldown (n2);\n"
      "endmodule\n"));
}

}  // namespace
