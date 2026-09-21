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

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A compound assignment adds to the enum variable and assigns the sum back,
// so the variable is an operand of a numerical expression: §6.19.4 auto-casts
// it to the base type there and requires a cast to assign the result to the
// variable, whose type the sum's is not. §6.19.3 states the cast for a value
// outside the enumeration, so it is the §6.19.4 rule the report cites.
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

// C + 1 is a numerical expression §6.19.4 permits, and assigning it back to an
// enum variable is what the same clause requires a cast for, since the sum's
// type is the base type and not the enumeration's.
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

// The expression need not name the variable it is assigned to: a member of the
// enumeration is an enum identifier used as part of an expression, which
// §6.19.4 auto-casts to the base type, so `Red + 1` is that clause's case too.
TEST(EnumNumericalExpr, EnumMemberExprAssignNoCastIsAClause6194Report) {
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

// The enumeration methods first, last, next and prev return a value of the
// enumeration type (§6.19.5), so `C.next + 1` is arithmetic on an enum value
// and the assignment back is §6.19.4's case. A walk that stopped at every
// member access as it does at `c.num()` would call this §6.19.3.
TEST(EnumNumericalExpr, EnumMethodResultExprAssignNoCastIsAClause6194Report) {
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

// A declaration's initializer is an assignment of the value to the variable,
// so an initializer that is arithmetic on an enum member is §6.19.4's case
// wherever the declaration stands: as a module item and as a procedural
// declaration, which two different walks judge.
TEST(EnumNumericalExpr, EnumExprInitializersAreClause6194Reports) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  Colors M = Green + 1;\n"
      "  initial begin\n"
      "    Colors P = Blue * 2;\n"
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

// An expression with no enum operand is an arbitrary expression of another
// type, whose cast §6.19.3 states; §6.19.4 speaks only of expressions an enum
// takes part in. A fix that cited §6.19.4 for every non-bare value fails here.
TEST(EnumNumericalExpr, IntegerExprAssignNoCastStaysAClause6193Report) {
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

// An increment is the same assignment written a third way, §11.4.2 having
// `C++` stand for `C = C + 1`, so it is reported under the same §6.19.4 rule.
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
