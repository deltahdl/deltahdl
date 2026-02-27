// §31.7: Enabling timing checks with conditioned events

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.3 Elab — timing_check_condition with &&&
// =============================================================================
// &&& bare condition elaborates
TEST(ElabA70503, TimingCheckConditionBareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// &&& with parenthesized scalar_timing_check_condition elaborates
TEST(ElabA70503, TimingCheckConditionParenthesizedElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& (en == 1'b1), posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// &&& with negation elaborates
TEST(ElabA70503, TimingCheckConditionNegationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& ~reset, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// &&& on both ref and data events elaborates
TEST(ElabA70503, ConditionBothEventsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// $width with controlled_timing_check_event and condition elaborates
TEST(ElabA70503, ControlledTimingCheckEventWidthCondElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(negedge rst &&& en, 20);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — combined edge + terminal range + condition
// =============================================================================
// Full combination: edge + bit-select terminal + &&& condition elaborates
TEST(ElabA70503, FullCombinationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, data[0] &&& reset, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
