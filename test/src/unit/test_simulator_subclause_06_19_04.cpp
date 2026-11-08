#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(i->value.ToUint64(), 5u);
}

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
  EXPECT_EQ(r->value.ToUint64(), 6u);
}

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
