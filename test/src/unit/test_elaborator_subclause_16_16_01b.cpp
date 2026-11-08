#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoUniqueClockReport =
    "the property has no unique semantic leading clock";

const char* const kHeader =
    "module m;\n"
    "  wire clk1, clk2;\n"
    "  logic a, b;\n"
    "  assign clk2 = clk1;\n";

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
