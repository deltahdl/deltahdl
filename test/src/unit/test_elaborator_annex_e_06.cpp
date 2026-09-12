#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DelayModeUnit_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kUnit);
}

TEST(Elaborator, DelayModeUnit_OverridesPath) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "`delay_mode_unit\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kUnit);
}

// C1 control/edge: with no directive in the source, elaboration propagates the
// unset delay mode (kNone) onto the module. This confirms the kUnit result of
// the tests above is caused by the directive being applied, not by the
// elaborator defaulting any particular mode onto every module.
TEST(Elaborator, DelayModeUnit_AbsentLeavesModeUnset) {
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
DelayModeDirective UnitCaseDelayMode(const RtlirDesign* design,
                                     std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

// E.6 applies the directive to the modules that follow it in the source, and
// to no other: a module declared before it has no delay mode however soon the
// directive follows its declaration, where every module used to take the
// compilation unit's last directive.
TEST(Elaborator, DelayModeUnit_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module ahead;\n"
      "endmodule\n"
      "`delay_mode_unit\n"
      "module behind;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(UnitCaseDelayMode(design, "ahead"), DelayModeDirective::kNone);
  EXPECT_EQ(UnitCaseDelayMode(design, "behind"), DelayModeDirective::kUnit);
}

// The same rule between two directives: a module declared under E.5's path
// mode keeps it when E.6's directive follows its declaration, and the module
// after that directive is the one in the unit mode. OverridesPath above has
// both directives before the one module; here the module between them tells
// the directive before it from the one after.
TEST(Elaborator, DelayModeUnit_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module routed;\n"
      "endmodule\n"
      "`delay_mode_unit\n"
      "module stepped;\n"
      "endmodule\n",
      f, /*top=*/"", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(UnitCaseDelayMode(design, "routed"), DelayModeDirective::kPath);
  EXPECT_EQ(UnitCaseDelayMode(design, "stepped"), DelayModeDirective::kUnit);
}

}  // namespace
