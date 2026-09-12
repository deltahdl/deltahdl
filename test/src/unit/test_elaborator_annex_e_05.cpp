#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DelayModePath_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
}

TEST(Elaborator, DelayModePath_OverridesDistributed) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_distributed\n"
      "`delay_mode_path\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
}

// Claim A edge case ("all modules that follow"): a single directive selects the
// path delay mode for every module that comes after it, not just the first.
// Both modules elaborated below should carry the path mode.
TEST(Elaborator, DelayModePath_AppliesToAllFollowingModules) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
  EXPECT_EQ(design->top_modules[1]->delay_mode, DelayModeDirective::kPath);
}

// The delay mode of the top module named `module`, or kNone where the design
// has no top of that name; the two cases below root every module as a top.
DelayModeDirective TopDelayMode(const RtlirDesign* design,
                                std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

// E.5 applies the directive to the modules that follow it in the source, and
// to no other: a module declared before it has no delay mode however soon the
// directive follows its declaration, where every module used to take the
// compilation unit's last directive.
TEST(Elaborator, DelayModePath_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module first;\n"
      "endmodule\n"
      "`delay_mode_path\n"
      "module second;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(TopDelayMode(design, "first"), DelayModeDirective::kNone);
  EXPECT_EQ(TopDelayMode(design, "second"), DelayModeDirective::kPath);
}

// The same rule between two directives: a module declared under E.4's
// distributed mode keeps it when E.5's directive follows its declaration, and
// the module after that directive is the one in the path mode. The case above
// this one, OverridesDistributed, has both directives before the one module;
// here the module between them tells the directive before it from the one
// after.
TEST(Elaborator, DelayModePath_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_distributed\n"
      "module spread;\n"
      "endmodule\n"
      "`delay_mode_path\n"
      "module pathed;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(TopDelayMode(design, "spread"), DelayModeDirective::kDistributed);
  EXPECT_EQ(TopDelayMode(design, "pathed"), DelayModeDirective::kPath);
}

}  // namespace
