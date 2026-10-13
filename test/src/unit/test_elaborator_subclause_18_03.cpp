#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr char kMessage[] =
    "a constraint subexpression holding a random variable shall be of an "
    "integral or real type";

// 18.3: a constraint's operands are integral or real, so a subexpression of
// another type that holds a random variable is an error, at the subexpression,
// whether it is a cast, a system function yielding a string, or a conditional
// choosing between strings.
TEST(ConstraintOperandTypes, ANonIntegralSubexpressionOverARandomVariable) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand bit [7:0] b;\n"
      "  randc bit [1:0] r;\n"
      "  string s;\n"
      "  constraint c1 { string'(r) == \"A\"; }\n"
      "  constraint c2 { $sformatf(\"%0d\", b) == s; }\n"
      "  constraint c3 { if (b > 1) { (b > 2 ? s : \"x\") == \"y\"; } }\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 5, "18.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 6, "18.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 7, "18.3"));
}

// A subexpression of another type is allowed where it holds no random
// variable and yields an integral or real result: a comparison of a string
// property, a cast of one, and a test of a random object handle, which is no
// random variable of the solve. A conditional and a system function of
// integral results are integral, whatever they read.
TEST(ConstraintOperandTypes, ANonIntegralSubexpressionWithoutOne) {
  EXPECT_TRUE(
      ElabOk("class D;\n"
             "  rand int y;\n"
             "endclass\n"
             "class C;\n"
             "  rand bit [7:0] b;\n"
             "  rand D d;\n"
             "  string s;\n"
             "  int n;\n"
             "  constraint c { s == \"abc\" -> b == 1;\n"
             "                 string'(n) != s;\n"
             "                 d != null -> d.y > b;\n"
             "                 (b > 3 ? 1 : 2) == $countones(b); }\n"
             "endclass\n"));
}

// 18.7: an inline constraint block is checked against the class of the object
// it randomizes, as the class's own blocks are.
TEST(ConstraintOperandTypes, AnInlineConstraintBlockIsChecked) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand bit [7:0] b;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial void'(obj.randomize() with { string'(b) == \"A\"; });\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 6, "18.3"));
}

}  // namespace
