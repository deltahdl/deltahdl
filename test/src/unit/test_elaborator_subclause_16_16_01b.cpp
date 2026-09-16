#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoUniqueClockReport =
    "the property has no unique semantic leading clock";

// The clause's example: clk2 is assigned clk1, so the two clocks have the
// same value at every time and are still not identical.
const char* const kHeader =
    "module m;\n"
    "  wire clk1, clk2;\n"
    "  logic a, b;\n"
    "  assign clk2 = clk1;\n";

// §16.16.1: the clause's a1, @(clk1) a and @(clk2) b, has the leading
// clocks clk1 and clk2, not identical though of the same value, so it has
// no unique semantic leading clock and is illegal; its a2, @(clk1) a and
// @(clk1) b, has clk1 alone and is legal.
TEST(SemanticLeadingClockElaboration,
     AStaticStatementNeedsIdenticalLeadingClocks) {
  ElabFixture f;
  Elaborate(std::string(kHeader) +
                "  a1: assert property (@(clk1) a and @(clk2) b);\n"
                "  a2: assert property (@(clk1) a and @(clk1) b);\n"
                "endmodule\n",
            f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoUniqueClockReport, 5, "16.16.1"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoUniqueClockReport, 6, "16.16.1"));
}

// §16.16.1: in an always at posedge clk1 the inherited clock is the
// inferred posedge clk1, which the clause's a3, a and @(posedge clk2) b,
// pairs with a clock that is not identical, so a3 is illegal under
// §16.16's rule that a multiclocked property takes no inferred clock,
// while its a4, a and @(posedge clk1) b, names the inferred clock alone
// and is legal.
TEST(SemanticLeadingClockElaboration,
     AProceduralStatementNeedsTheInferredClockAlone) {
  ElabFixture f;
  Elaborate(std::string(kHeader) +
                "  always @(posedge clk1) begin\n"
                "    a3: assert property (a and @(posedge clk2) b);\n"
                "    a4: assert property (a and @(posedge clk1) b);\n"
                "  end\n"
                "endmodule\n",
            f);
  const char* const kInferredReport =
      "a multiclocked property may not take a contextually inferred "
      "leading clocking event";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kInferredReport, 6, "16.16"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kInferredReport, 7, "16.16"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoUniqueClockReport, 7, "16.16.1"));
}

// §16.16.1: an instance's leading clocks are its body's, so a property
// declared with two leading clocks is illegal wherever it is asserted, and
// a sequence whose clock changes after its first tick has the one leading
// clock and is legal.
TEST(SemanticLeadingClockElaboration, AnInstanceCarriesItsBodysClocks) {
  ElabFixture f;
  Elaborate(std::string(kHeader) +
                "  property two;\n"
                "    @(clk1) a and @(clk2) b;\n"
                "  endproperty\n"
                "  sequence switching;\n"
                "    @(posedge clk1) a ##1 @(negedge clk1) b;\n"
                "  endsequence\n"
                "  a5: assert property (two);\n"
                "  c1: cover property (switching);\n"
                "endmodule\n",
            f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoUniqueClockReport, 11, "16.16.1"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoUniqueClockReport, 12, "16.16.1"));
}

}  // namespace
