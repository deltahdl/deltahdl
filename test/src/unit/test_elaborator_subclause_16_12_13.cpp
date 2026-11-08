#include <gtest/gtest.h>

#include "elaborator/eventually_range.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EventuallyRange, WeakEventuallyAllowsBoundedRange) {
  EXPECT_TRUE(IsEventuallyRangeWellFormed(MakeEventuallyBound(5), false));
}

TEST(EventuallyRange, WeakEventuallyRejectsUnboundedMaximum) {
  EXPECT_FALSE(IsEventuallyRangeWellFormed(MakeEventuallyDollar(), false));
}

TEST(EventuallyRange, StrongEventuallyAllowsUnboundedMaximum) {
  EXPECT_TRUE(IsEventuallyRangeWellFormed(MakeEventuallyDollar(), true));
}

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
