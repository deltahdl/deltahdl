#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.6, Table 31-6: the two $recrem limits (recovery_limit then
// removal_limit) are each a plain constant expression -- not the non-negative
// constant expression that governs standalone $removal and $recovery. The
// subclause text states $recrem can accept negative limit values. The
// well-formed two-positive-limit form is the baseline accepting path and must
// elaborate cleanly. Built from real specify-block source and driven through
// elaboration.
TEST(RecremTimingCheckElaboration, PositiveLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clr, posedge clk, 10, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A negative recovery (first) limit is accepted. The sign-validation passes
// that reject a negative $removal or $recovery limit must deliberately skip
// $recrem, so this same input -- illegal for those standalone checks --
// elaborates without error. Built from real source and driven through
// elaboration so the folded negative reaches the validator layer.
TEST(RecremTimingCheckElaboration, NegativeRecoveryLimitAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clr, posedge clk, -5, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A negative removal (second) limit is likewise accepted -- the second limit
// slot admits a negative constant just as the first does. This is a distinct
// input form from the negative-recovery case above (the negative sits in the
// other of the two mandatory limit positions).
TEST(RecremTimingCheckElaboration, NegativeRemovalLimitAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clr, posedge clk, 5, -3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The negative limit may be produced by a specparam that folds to a negative
// value rather than by a bare literal. Built from real specparam syntax so the
// elaborator folds the reference before any sign check runs; $recrem accepts it
// where the identically-produced input would be rejected for $removal or
// $recovery. This exercises the specparam constant operand form, distinct from
// the bare negative literals above.
TEST(RecremTimingCheckElaboration, NegativeSpecparamLimitAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tREC = -4;\n"
      "    $recrem(posedge clr, posedge clk, tREC, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
