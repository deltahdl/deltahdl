// Tests for §6.19.4 "Enumerated types in numerical expressions": "Elements of
// enumerated type variables can be used in numerical expressions. The value
// used in the expression is the numerical value associated with the enumerated
// value ... An enum variable or identifier used as part of an expression is
// automatically cast to the base type of the enum declaration (either
// explicitly or using int as the default)."
//
// The restriction §6.19.4 closes with -- "A cast shall be required for an
// expression that is assigned to an enum variable where the type of the
// expression is not equivalent to the enumeration type of the variable" --
// restates §6.19.3, "assignment of arbitrary expressions to an enumerated
// variable requires an explicit cast". One elaborator path enforces both, and
// it names §6.19.3, so that is the subclause the rejections below read back.

#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// A compound assignment assigns an expression to the enum variable, which
// §6.19.3 admits only through an explicit cast.
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
                            6, "6.19.3"));
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

// C + 1 is a numerical expression §6.19.4 permits, and assigning it back to an
// enum variable is what §6.19.3 requires a cast for.
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

// 6.19.4: a cast to an enum type converts the expression to the base type
// without checking the value's validity, so casting an out-of-range value into
// an enum is accepted. Here Su (a Week member, value 6) is cast into the
// three-member Colors enum; the cast is legal even though 6 names no Colors.
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

// 6.19.4: the auto-cast-to-base-type rule covers an enum whose base type is
// declared explicitly, not only the int default. An explicit-base enum member
// used in arithmetic and assigned to an integer elaborates without a cast,
// because the member auto-casts to its (explicit) base type.
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

// An increment is the same assignment written a third way, and it is reported
// under the same §6.19.3 requirement.
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
                            6, "6.19.3"));
}

}  // namespace
