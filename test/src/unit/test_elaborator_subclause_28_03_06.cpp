#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GateArrayConnection, MatchingWidthBroadcastElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, DistributeWidthElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] y, a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, MixedBroadcastAndDistributePerTerminalElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, ParameterizedArrayRangeDistributesAcrossInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter N = 4;\n"
      "  wire [3:0] y, a, b;\n"
      "  and g[0:N-1](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, ParameterizedArrayRangeTooFewBitsIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter N = 4;\n"
      "  wire [1:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:N-1](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            5, "28.3.6"));
}

TEST(GateArrayConnection, TooFewBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [1:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, TooManyBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, ScalarInterconnectCannotBroadcastAcrossArray) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  interconnect ic;\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect terminal of a gate or primitive "
                            "instance array",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, InterconnectWidthEqualToArrayLengthElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  interconnect [3:0] ic;\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, ASelectOrConcatenationOfTheWrongWidthIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire a, b, c, o;\n"
      "  and g[3:0] (y[2:0], a, b);\n"
      "  and h[3:0] (o, {a, b}, c);\n"
      "endmodule\n",
      f);
  for (int line : {4, 5}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "gate or primitive array terminal width does not "
                              "match",
                              line, "28.3.6"))
        << line;
  }
}

TEST(GateArrayConnection, AnOperatorExpressionOfTheWrongWidthIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [2:0] s;\n"
      "  wire o;\n"
      "  and h[3:0] (o, ~s, 1'b1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            4, "28.3.6"));
}

TEST(GateArrayConnection, ALiteralOfTheWrongWidthIsReported) {
  for (const char* literal : {"2'b01", "1"}) {
    ElabFixture f;
    Elaborate(std::string("module m;\n"
                          "  wire [3:0] o;\n"
                          "  wire a;\n"
                          "  and g[3:0] (o, ") +
                  literal +
                  ", a);\n"
                  "endmodule\n",
              f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "gate or primitive array terminal width does not "
                              "match",
                              4, "28.3.6"))
        << literal;
  }
}

TEST(GateArrayConnection, ASubarrayOfTheWrongWidthIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [1:0][1:0] p;\n"
      "  wire [3:0] o;\n"
      "  wire a;\n"
      "  and g[3:0] (o, p[1], a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate or primitive array terminal width does not "
                            "match",
                            5, "28.3.6"));
}

}  // namespace
