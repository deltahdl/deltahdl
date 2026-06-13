#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

// E4-C1: the directive selects the distributed mode for *all* modules that
// follow it, not just the first. A parent and the child it instantiates are
// both elaborated under the directive, so both carry the distributed mode.
TEST(Elaborator, DelayModeDistributed_AppliesToAllFollowingModules) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_distributed\n"
      "module child;\n"
      "endmodule\n"
      "module parent;\n"
      "  child c();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* parent = design->top_modules[0];
  EXPECT_EQ(parent->delay_mode, DelayModeDirective::kDistributed);
  ASSERT_FALSE(parent->children.empty());
  ASSERT_NE(parent->children[0].resolved, nullptr);
  EXPECT_EQ(parent->children[0].resolved->delay_mode,
            DelayModeDirective::kDistributed);
}

}
