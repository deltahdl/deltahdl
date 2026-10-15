#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

// §28.9 makes a cmos switch an nmos and a pmos sharing the data input and the
// output with a control each, and an rcmos an rnmos and an rpmos, so the
// switch elaborates to the two continuous assignments of those switches, both
// driving the first terminal.
void ExpectPairedMosSwitches(std::string_view keyword, bool resistive) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  " +
          std::string(keyword) +
          " c1(out, data, nctrl, pctrl);\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  for (const auto& ca : mod->assigns) {
    ASSERT_NE(ca.lhs, nullptr);
    EXPECT_EQ(ca.lhs->text, "out");
    EXPECT_EQ(ca.from_resistive_switch, resistive);
    EXPECT_EQ(ca.from_nonresistive_switch, !resistive);
    ASSERT_NE(ca.three_state_pass, nullptr);
    EXPECT_EQ(ca.three_state_pass->text, "data");
  }
  ASSERT_NE(mod->assigns[0].three_state_ctrl, nullptr);
  EXPECT_EQ(mod->assigns[0].three_state_ctrl->text, "nctrl");
  ASSERT_NE(mod->assigns[1].three_state_ctrl, nullptr);
  EXPECT_EQ(mod->assigns[1].three_state_ctrl->text, "pctrl");
}

TEST(CmosSwitchElaboration, CmosElaboratesToAnNmosAndAPmos) {
  ExpectPairedMosSwitches("cmos", false);
}

TEST(CmosSwitchElaboration, RcmosElaboratesToAnRnmosAndAnRpmos) {
  ExpectPairedMosSwitches("rcmos", true);
}

// The nmos half conducts on a 1 of its control and the pmos half on a 0, each
// written as Table 28-6 reads it: z data drives z whatever the control, and
// otherwise the control selects the data or z.
TEST(CmosSwitchElaboration, CmosHalvesConductOnOppositeControlValues) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  for (size_t k = 0; k < 2; ++k) {
    const Expr* rhs = mod->assigns[k].rhs;
    ASSERT_NE(rhs, nullptr);
    ASSERT_EQ(rhs->kind, ExprKind::kTernary);
    ASSERT_NE(rhs->condition, nullptr);
    EXPECT_EQ(rhs->condition->op, TokenKind::kEqEqEq);
    ASSERT_NE(rhs->false_expr, nullptr);
    ASSERT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
    const Expr* pass =
        k == 0 ? rhs->false_expr->true_expr : rhs->false_expr->false_expr;
    ASSERT_NE(pass, nullptr);
    EXPECT_EQ(pass->text, "data");
  }
}

}  // namespace
