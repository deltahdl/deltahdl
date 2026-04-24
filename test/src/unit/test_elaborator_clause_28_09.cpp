// §28.9

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A single cmos instance lowers to exactly one continuous assign driving the
// output from the ternary (ncontrol ? data : (pcontrol ? 'z : data)).
TEST(CmosSwitchElaboration, CmosEmitsSingleContinuousAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 1u);
}

TEST(CmosSwitchElaboration, RcmosEmitsSingleContinuousAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 1u);
}

// The first terminal is the driven data output; pinning the LHS identifier
// guards against a reshuffling that would drive the wrong net.
TEST(CmosSwitchElaboration, CmosOutputIsFirstTerminal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_EQ(mod->assigns[0].lhs->text, "out");
}

// cmos collapses to the nmos+pmos pair: when ncontrol asserts, data wins;
// otherwise pcontrol selects between high-Z and data.
TEST(CmosSwitchElaboration, CmosLowersToNestedTernary) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->text, "nctrl");
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->true_expr->text, "data");
  ASSERT_NE(rhs->false_expr, nullptr);
  ASSERT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->condition, nullptr);
  EXPECT_EQ(rhs->false_expr->condition->text, "pctrl");
  ASSERT_NE(rhs->false_expr->true_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->true_expr->kind,
            ExprKind::kUnbasedUnsizedLiteral);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->false_expr->false_expr->text, "data");
}

// rcmos must lower to the same ternary shape as cmos; strength attenuation
// is modelled elsewhere and must not leak into the RHS structure.
TEST(CmosSwitchElaboration, RcmosLowersToNestedTernary) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->text, "nctrl");
  ASSERT_NE(rhs->false_expr, nullptr);
  ASSERT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->condition, nullptr);
  EXPECT_EQ(rhs->false_expr->condition->text, "pctrl");
}

}  // namespace
