#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// 6.19.4: an enumeration element used in a numerical expression contributes
// the numerical value associated with the enumerated value. The canonical
// example declares Colors {red..black}; blue has value 2, so blue*3 is 6 and
// yellow(3) + green(1) is 4.
TEST(EnumNumericalExpr, ElementValueUsedInArithmetic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {red, green, blue, yellow, white, black} Colors;\n"
      "  Colors col;\n"
      "  integer a, b;\n"
      "  initial begin\n"
      "    a = blue * 3;\n"
      "    col = yellow;\n"
      "    b = col + green;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 6u);
  EXPECT_EQ(b->value.ToUint64(), 4u);
}

// 6.19.4: an enum variable used as part of an expression is automatically cast
// to the base type of its enum (int by default). Two enum operands of distinct
// enum types may therefore be combined arithmetically into an integral result.
TEST(EnumNumericalExpr, CrossEnumOperandsAutocastToInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  typedef enum {Mo, Tu, We, Th, Fr, Sa, Su} Week;\n"
      "  Colors C;\n"
      "  Week W;\n"
      "  int I;\n"
      "  initial begin\n"
      "    C = Blue;\n"
      "    W = Th;\n"
      "    I = C + W;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* i = f.ctx.FindVariable("I");
  ASSERT_NE(i, nullptr);
  // Blue == 2, Th == 3 -> 2 + 3 == 5.
  EXPECT_EQ(i->value.ToUint64(), 5u);
}

// 6.19.4: a cast to an enum converts the expression to the enum's base type
// without checking that the value names a member, so the out-of-range value
// survives the cast at run time. Su belongs to Week (value 6); casting it into
// the three-member Colors enum leaves Colors variable C holding 6, not a
// clamped or rejected value.
TEST(EnumNumericalExpr, OutOfRangeCastPreservesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {Red, Green, Blue} Colors;\n"
      "  typedef enum {Mo, Tu, We, Th, Fr, Sa, Su} Week;\n"
      "  Colors C;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    C = Colors'(Su);\n"
      "    r = C;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  // Su == 6; the cast does not validate membership, so C keeps 6.
  EXPECT_EQ(r->value.ToUint64(), 6u);
}

// 6.19.4: an enum element used in an expression auto-casts to the enum's base
// type, which may be declared explicitly rather than defaulting to int. Here
// the base is bit [3:0] with gold == 5, so gold * 2 evaluates to 10 using the
// member's numerical value.
TEST(EnumNumericalExpr, ExplicitBaseTypeElementValueInArithmetic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum bit [3:0] {bronze = 3, silver, gold} medal_t;\n"
      "  medal_t medal;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    medal = gold;\n"
      "    x = gold * 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 10u);
}

}  // namespace
