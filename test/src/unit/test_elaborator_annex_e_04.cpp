#include <string_view>

#include "elaborator/rtlir.h"
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

// The delay mode of the top module named `module`, or kNone where the design
// has no top of that name.
DelayModeDirective ModeOf(const RtlirDesign* design, std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

// E.4 applies the directive to the modules that follow it in the source, and
// to no other: a module declared before the directive has no delay mode
// whatever comes after its declaration, where every module used to take the
// compilation unit's last directive.
TEST(Elaborator, DelayModeDistributed_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module earlier;\n"
      "endmodule\n"
      "`delay_mode_distributed\n"
      "module later;\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ModeOf(design, "earlier"), DelayModeDirective::kNone);
  EXPECT_EQ(ModeOf(design, "later"), DelayModeDirective::kDistributed);
}

// The same rule between two directives: a module declared under E.5's path
// mode keeps it when E.4's directive follows its declaration, and the module
// after that directive is the one in the distributed mode.
TEST(Elaborator, DelayModeDistributed_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module p;\n"
      "endmodule\n"
      "`delay_mode_distributed\n"
      "module d;\n"
      "endmodule\n",
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ModeOf(design, "p"), DelayModeDirective::kPath);
  EXPECT_EQ(ModeOf(design, "d"), DelayModeDirective::kDistributed);
}

}  // namespace
