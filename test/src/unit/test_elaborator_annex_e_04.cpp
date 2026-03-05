#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §E.4: delay_mode_distributed propagates to elaborated module.
TEST(Elaborator, DelayModeDistributed_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_distributed\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode,
            DelayModeDirective::kDistributed);
}

// §E.4: no directive means kNone.
TEST(Elaborator, DelayMode_DefaultIsNone) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

// §E.4: delay_mode_distributed with other Annex E directives.
TEST(Elaborator, DelayModeDistributed_WithOtherDirectives) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 100\n"
      "`delay_mode_distributed\n"
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode,
            DelayModeDirective::kDistributed);
}

}  // namespace
