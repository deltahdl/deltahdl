#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.3, Table 31-3: each of the two $setuphold limits is a constant
// expression. Unlike the non-negative rule that governs standalone $setup and
// $hold, the subclause text says $setuphold can accept negative limit values.
// The well-formed two-positive-limit form is the baseline accepting path and
// must elaborate cleanly.
TEST(SetupholdTimingCheckElaboration, PositiveLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A negative setup (first) limit is accepted. The sign-validation pass that
// rejects a negative $hold limit must deliberately skip $setuphold, so this
// same input -- illegal for $hold -- elaborates without error. Built from real
// source and driven through elaboration so the folded negative reaches the
// validator.
TEST(SetupholdTimingCheckElaboration, NegativeSetupLimitAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, -5, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A negative hold (second) limit is likewise accepted -- the second limit slot
// admits a negative constant just as the first does. This is a distinct input
// form from the negative-setup case above (the negative sits in the other of
// the two mandatory limit positions).
TEST(SetupholdTimingCheckElaboration, NegativeHoldLimitAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 5, -3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The negative limit may be produced by a §31.2 specparam that folds to a
// negative value. Built from real specparam syntax so the elaborator folds the
// reference before the sign check runs; $setuphold accepts it where $hold
// rejects the identically-produced input. This exercises the specparam operand
// form, distinct from the bare negative literals above.
TEST(SetupholdTimingCheckElaboration, NegativeSpecparamLimitAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSU = -4;\n"
      "    $setuphold(posedge clk, data, tSU, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
