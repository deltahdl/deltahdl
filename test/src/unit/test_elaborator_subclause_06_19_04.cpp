#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
