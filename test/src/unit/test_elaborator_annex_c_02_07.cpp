#include "fixture_elaborator.h"

// Annex C.2.7 - "always statement in checkers".
//
// The general-purpose always procedure in a checker was permitted by IEEE Std
// 1800-2009, but the specialized always_comb/always_latch/always_ff forms were
// forbidden. This version of the standard adds the three specialized forms to
// checkers and, because a general always in a checker would have carried the
// always_ff limitations anyway, deprecates and removes the general always
// procedure from checkers. The implementable rule: a plain always inside a
// checker body is rejected, while the three specialized forms are accepted.
//
// The rule is enforced in the elaborator's checker-body composition pass
// (src/elaborator/elaborator_items.cpp), the same place the other "what may
// appear in a checker body" rules live. These tests observe that production
// code by elaborating each form and checking whether an error was produced.

namespace {

TEST(AlwaysProcedureInCheckers, GeneralAlwaysInCheckerIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a;\n"
      "  always @(posedge clk) a <= 1'b1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, AlwaysFfInCheckerIsAccepted) {
  // Contrast with GeneralAlwaysInCheckerIsRejected: identical body, only the
  // procedure keyword changes. always_ff is one of the three specialized forms
  // added for checkers, so it must elaborate cleanly.
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a;\n"
      "  always_ff @(posedge clk) a <= 1'b1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, AlwaysCombInCheckerIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  logic a, b;\n"
      "  always_comb a = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, AlwaysLatchInCheckerIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic en);\n"
      "  logic a, b;\n"
      "  always_latch if (en) a = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, GeneralAlwaysOutsideCheckerIsStillAllowed) {
  // The deprecation is scoped to checker bodies. A general always procedure in
  // an ordinary module remains legal, proving the rejection keys on the checker
  // context and not on the always keyword itself.
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk);\n"
      "  logic a;\n"
      "  always @(posedge clk) a <= 1'b1;\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers,
     GeneralAlwaysRejectedAlongsideAcceptedSpecializedForms) {
  // Integration: a checker mixing an accepted always_comb with a forbidden
  // general always is still rejected. The presence of valid specialized forms
  // does not suppress the general-always diagnostic.
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a, b, c;\n"
      "  always_comb c = b;\n"
      "  always @(posedge clk) a <= b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
