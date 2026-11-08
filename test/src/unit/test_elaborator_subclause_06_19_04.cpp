#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EnumNumericalExpr, EnumArithNoCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = a;\n"
      "    val += 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "compound assignment to enum variable without cast",
                            6, "6.19.4"));
}

TEST(EnumNumericalExpr, EnumToIntAutocast_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  integer a;\n"
      "  initial a = BLUE * 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumAssignToInt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {A, B, C} my_e;\n"
      "  int x;\n"
      "  initial x = B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumIntComparison_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {X, Y, Z} vals;\n"
      "  initial begin\n"
      "    if (1 == Y) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumExprAssignNoCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = Red;\n"
      "    C = C + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.4"));
}

TEST(EnumNumericalExpr,
     EnumMemberExprAssignNoCastIsANumericalExpressionReport) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = Red + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.4"));
}

TEST(EnumNumericalExpr,
     EnumMethodResultExprAssignNoCastIsANumericalExpressionReport) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = Red;\n"
      "    C = C.next + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.4"));
}

TEST(EnumNumericalExpr, EnumExprInitializersAreNumericalExpressionReports) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  Colors M = Green + 1;\n"
      "  initial begin\n"
      "    static Colors P = Blue * 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.4"));
}

TEST(EnumNumericalExpr, IntegerExprAssignNoCastStaysATypeCheckingReport) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  int x;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = x + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(EnumNumericalExpr, EnumCastExprAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = Red;\n"
      "    C = Colors'(C + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumAddTwoEnumsToInt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  typedef enum {Mo, Tu, We, Th, Fr, Sa, Su} Week;\n"
      "  int I;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    Week W;\n"
      "    C = Red;\n"
      "    W = Mo;\n"
      "    I = C + W;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumCastOutOfRange_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  typedef enum {Mo, Tu, We, Th, Fr, Sa, Su} Week;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = Colors'(Su);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumExplicitBaseAutocast_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum bit [3:0] {lo = 1, hi} e;\n"
      "  int a;\n"
      "  initial a = hi * 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumNumericalExpr, EnumIncrementNoCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  initial begin\n"
      "    Colors C;\n"
      "    C = Red;\n"
      "    C++;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "increment/decrement of enum variable without cast",
                            6, "6.19.4"));
}

}  // namespace
