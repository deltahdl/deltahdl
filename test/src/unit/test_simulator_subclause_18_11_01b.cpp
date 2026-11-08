#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InlineConstraintCheckerRun, NullChecksTheRelationOnTheCurrentValues) {
  SimFixture f;
  std::string out = RunCapture(
      "class CA;\n"
      "  rand byte x, y;\n"
      "  byte v, w;\n"
      "  constraint c1 { x < v && y > w; }\n"
      "endclass\n"
      "module t;\n"
      "  int holds, fails, kept_a, kept_b;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
      "    a.x = 10; a.v = 20; a.y = 30; a.w = 5;\n"
      "    holds = a.randomize(null);\n"
      "    kept_a = a.x == 10 && a.v == 20 && a.y == 30 && a.w == 5;\n"
      "    a.v = 5;\n"
      "    fails = a.randomize(null);\n"
      "    kept_b = a.x == 10 && a.v == 5 && a.y == 30 && a.w == 5;\n"
      "    $display(\"%0d %0d %0d %0d\", holds, kept_a, fails, kept_b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 0 1\n");
}

TEST(InlineConstraintCheckerRun, NoRandomVariablesMakesTheMethodAChecker) {
  SimFixture f;
  std::string out = RunCapture(
      "class Ordered;\n"
      "  byte p, q;\n"
      "  constraint order { p < q; }\n"
      "endclass\n"
      "module t;\n"
      "  int holds, fails, kept;\n"
      "  initial begin\n"
      "    static Ordered o = new;\n"
      "    o.p = 1; o.q = 2;\n"
      "    holds = o.randomize();\n"
      "    o.p = 3;\n"
      "    fails = o.randomize();\n"
      "    kept = o.p == 3 && o.q == 2;\n"
      "    $display(\"%0d %0d %0d\", holds, fails, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1\n");
}

}  // namespace
