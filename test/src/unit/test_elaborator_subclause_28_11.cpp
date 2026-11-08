#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(LogicStrengthModeling, ValidStrength0Strength1PairElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (weak0, pull1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LogicStrengthModeling, Highz0Highz1PairIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(LogicStrengthModeling, Highz1Highz0PairIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz1, highz0) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(LogicStrengthModeling, Highz0WithDrivingStrength1IsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LogicStrengthModeling, DrivingStrength0WithHighz1IsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LogicStrengthModeling, Highz0Highz1OnContinuousAssignIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, y;\n"
      "  assign (highz0, highz1) y = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(LogicStrengthModeling, DrivingPairOnContinuousAssignIsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, y;\n"
      "  assign (strong0, weak1) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LogicStrengthModeling, Highz0Highz1OnNetDeclarationIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  wire (highz0, highz1) w = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(LogicStrengthModeling, DrivingPairOnNetDeclarationIsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  wire (pull0, highz1) w = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
