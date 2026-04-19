#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.9.2: the elaborator must accept a $setuphold invocation whose
// sixth positional slot carries the timestamp_condition introduced by
// this subclause, even when the seventh slot is left unset.
TEST(NegativeTimingConditions, SetupholdTimestampConditionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.9.2: populating both condition slots must elaborate as well, so
// the pair can reach the simulator for the runtime rules this subclause
// describes.
TEST(NegativeTimingConditions, SetupholdBothConditionsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.9.2 via §31.9's identical-behaviour rule: $recrem must accept
// the same paired condition arguments that $setuphold does, or the
// negative-hold recovery/removal case would have no way to pair the
// condition with the correct delayed signal.
TEST(NegativeTimingConditions, RecremBothConditionsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.9.2: the comma-first form that leaves the timestamp slot empty
// while populating the timecheck slot — mirroring the LRM's
// negative-setup example — must pass through elaboration so the
// simulator receives the exact association the subclause describes.
TEST(NegativeTimingConditions, SetupholdOmittedTimestampPopulatedTimecheckElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, -10, 20, ntfr, , 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
