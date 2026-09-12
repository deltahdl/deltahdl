#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DelayModeZero_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_zero\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kZero);
}

TEST(Elaborator, DelayModeZero_OverridesUnit) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "`delay_mode_zero\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kZero);
}

// C1 (edge, negative control): the zero delay mode reaches a module only
// because the directive selected it. With no directive ahead of the module,
// elaboration leaves the module's delay mode unset, confirming `delay_mode_zero
// is what drives the kZero result above rather than a default.
TEST(Elaborator, DelayModeZero_AbsentLeavesModeUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

// The delay mode of the top module named `module`, or kNone where the design
// has no top of that name; the cases below root every module as a top.
DelayModeDirective ZeroCaseDelayMode(const RtlirDesign* design,
                                     std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

// E.7 applies the directive to the modules that follow it in the source, and
// to no other: a module declared before it has no delay mode however soon the
// directive follows its declaration, where every module used to take the
// compilation unit's last directive.
TEST(Elaborator, DelayModeZero_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module upstream;\n"
      "endmodule\n"
      "`delay_mode_zero\n"
      "module downstream;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ZeroCaseDelayMode(design, "upstream"), DelayModeDirective::kNone);
  EXPECT_EQ(ZeroCaseDelayMode(design, "downstream"), DelayModeDirective::kZero);
}

// The same rule between two directives: a module declared under E.6's unit
// mode keeps it when E.7's directive follows its declaration, and the module
// after that directive is the one in the zero mode. OverridesUnit above has
// both directives before the one module; here the module between them tells
// the directive before it from the one after.
TEST(Elaborator, DelayModeZero_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "module ticking;\n"
      "endmodule\n"
      "`delay_mode_zero\n"
      "module instant;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ZeroCaseDelayMode(design, "ticking"), DelayModeDirective::kUnit);
  EXPECT_EQ(ZeroCaseDelayMode(design, "instant"), DelayModeDirective::kZero);
}

}  // namespace
