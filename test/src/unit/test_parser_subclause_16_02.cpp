#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssertionKindsParsing, ImmediateRestrictIsRefused) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial restrict (a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "restrict has no immediate", 3, "16.2"));
}

TEST(AssertionKindsParsing, RestrictPropertyIsAcceptedWithoutAReport) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(ReportedWarning(r.diags, "concurrent assertion is not evaluated",
                               3, "16.14"));
}

TEST(AssertionKindsParsing, ImmediateAssertAssumeAndCoverAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    assert (a);\n"
      "    assume (a);\n"
      "    cover (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
