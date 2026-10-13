#include <gtest/gtest.h>

#include "elaborator/eventually_range.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.12.13: a weak `eventually` with a bounded range is well-formed.
TEST(EventuallyRange, WeakEventuallyAllowsBoundedRange) {
  EXPECT_TRUE(
      IsEventuallyRangeWellFormed(MakeEventuallyBound(5), /*strong=*/false));
}

// §16.12.13: a weak eventually needs a finite range, so a `$` upper
// bound is rejected for `eventually` (the `eventually [2:$]` form is illegal).
TEST(EventuallyRange, WeakEventuallyRejectsUnboundedMaximum) {
  EXPECT_FALSE(
      IsEventuallyRangeWellFormed(MakeEventuallyDollar(), /*strong=*/false));
}

// §16.12.13: the range for a strong eventually may be unbounded, so a `$` upper
// bound is accepted for `s_eventually` even though the same bound is illegal
// for the weak form.
TEST(EventuallyRange, StrongEventuallyAllowsUnboundedMaximum) {
  EXPECT_TRUE(
      IsEventuallyRangeWellFormed(MakeEventuallyDollar(), /*strong=*/true));
}

// §16.12.13: the bounds of a ranged eventually written as parameters are
// non-negative: [NEG:HI] has the minimum -1, while [0:HI] is legal.
TEST(EventuallyRangeElaboration, ANegativeParameterBoundIsReported) {
  const char* const kReport =
      "eventually range bounds shall be non-negative integer constant "
      "expressions, the minimum no greater than the maximum";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  localparam int NEG = -1, HI = 2;\n"
      "  a1: assert property (@(posedge clk) s_eventually [NEG:HI] a);\n"
      "  a2: assert property (@(posedge clk) s_eventually [0:HI] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.12.13"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.13"));
}

}  // namespace
