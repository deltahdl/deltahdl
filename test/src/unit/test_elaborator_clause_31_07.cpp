#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.7 Syntax 31-16: a plain-expression `&&&` condition elaborates without
// disturbing the surrounding $setup invocation.
TEST(ConditionedTimingCheckElaboration, TimingCheckConditionBareElaborates) {
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

// §31.7 Syntax 31-16: a parenthesized `expression == scalar_constant`
// condition elaborates without triggering errors.
TEST(ConditionedTimingCheckElaboration,
     TimingCheckConditionParenthesizedElaborates) {
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

// §31.7 Syntax 31-16: the `~ expression` form elaborates as a valid
// scalar_timing_check_condition.
TEST(ConditionedTimingCheckElaboration,
     TimingCheckConditionNegationElaborates) {
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

// §31.7 Syntax 31-16: a timing check may carry a `&&&` condition on each of
// its two timing_check_event operands; the elaborator must accept both.
TEST(ConditionedTimingCheckElaboration, ConditionBothEventsElaborates) {
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

// §31.7 Syntax 31-16: the `controlled_timing_check_event` production — used
// by $width's single event — accepts the optional `&&&` condition.
TEST(ConditionedTimingCheckElaboration,
     ControlledTimingCheckEventWidthCondElaborates) {
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

// §31.7 Syntax 31-16: the deterministic case-equality form `===` elaborates
// as a scalar_timing_check_condition operand.
TEST(ConditionedTimingCheckElaboration, ScalarConditionCaseEqualityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& (en === 1'b1), posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.7 Syntax 31-16: a `&&&` timing_check_condition composes with the
// `edge` keyword on the same timing_check_event_control and elaborates
// cleanly.
TEST(ConditionedTimingCheckElaboration, EdgeKeywordWithConditionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge clk &&& en, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.7 Syntax 31-16: the nondeterministic inequality form `!=` survives
// elaboration as a valid scalar_timing_check_condition operand.
TEST(ConditionedTimingCheckElaboration, InequalityConditionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& (en != 1'b0), posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.7 Syntax 31-16: the deterministic case-inequality form `!==`
// survives elaboration as a valid scalar_timing_check_condition operand.
TEST(ConditionedTimingCheckElaboration, CaseInequalityConditionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& (en !== 1'b0), posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.7: the conditioning value may be a multibit signal, in which case
// only the LSB is consulted. Elaboration must accept the multibit signal
// without a width error.
TEST(ConditionedTimingCheckElaboration, MultibitConditioningSignalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] en;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
