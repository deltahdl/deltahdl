#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckElaboration, TimeskewElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, TimeskewSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 7;\n"
      "    $timeskew(posedge clk1, posedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, TimeskewZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, TimeskewNegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$timeskew timing check limit must be a non-negative", 3, "31.4.2"));
}

TEST(SystemTimingCheckElaboration, TimeskewNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = -3;\n"
      "    $timeskew(posedge clk1, posedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$timeskew timing check limit must be a non-negative", 4, "31.4.2"));
}

TEST(SystemTimingCheckElaboration,
     TimeskewNonNegativeBinaryExprLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 3 + 4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, TimeskewNegativeBinaryExprLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 2 - 9);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$timeskew timing check limit must be a non-negative", 3, "31.4.2"));
}

TEST(SystemTimingCheckElaboration,
     TimeskewNotifierFromDeclaredVariableElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg ntfr;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, TimeskewNetOrVariableLimitRejected) {
  for (const char* name : {"w", "v"}) {
    ElabFixture f;
    std::string src =
        "module m(input clk, input d);\n"
        "  wire [7:0] w;\n"
        "  logic [7:0] v;\n"
        "  specify\n"
        "    $timeskew(posedge clk, d, ";
    src += name;
    src +=
        ");\n"
        "  endspecify\n"
        "endmodule\n";
    ElaborateSrc(src, f);
    std::string msg = "timing check limit operand '";
    msg += name;
    msg += "' is not a specparam";
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 5, "31.2")) << name;
  }
}

}  // namespace
