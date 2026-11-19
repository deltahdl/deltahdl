#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckElaboration, SkewZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, SkewNegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.4.1"));
}

TEST(SystemTimingCheckElaboration, SkewNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = -3;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.4.1"));
}

TEST(SystemTimingCheckElaboration, SkewNonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 4;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, SkewArithmeticLiteralLimitFoldsNegative) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 3 - 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.4.1"));
}

TEST(SystemTimingCheckElaboration, SkewSpecparamArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 6;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew - 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, SkewNetOrVariableLimitRejected) {
  for (const char* name : {"w", "v"}) {
    ElabFixture f;
    std::string src =
        "module m(input clk, input d);\n"
        "  wire [7:0] w;\n"
        "  logic [7:0] v;\n"
        "  specify\n"
        "    $skew(posedge clk, d, ";
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
