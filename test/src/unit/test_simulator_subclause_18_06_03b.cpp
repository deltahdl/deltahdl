#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.6.3: a random variable declared static is shared by all instances of
// the class, and each randomize() call changes it in every instance: over
// 32 rounds of a call on each of two Shared, both read the same v after
// every call, and a call on the second changes what the first reads in
// some round, as the design test/src/e2e/randomization_behavior.sv runs it.
TEST(RandomizationBehaviorRun, AStaticVariableChangesInEveryInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "class Shared;\n"
      "  static rand bit [7:0] v;\n"
      "  rand bit [7:0] own;\n"
      "endclass\n"
      "module t;\n"
      "  int agree = 0, changed = 0, before;\n"
      "  initial begin\n"
      "    Shared s1 = new;\n"
      "    Shared s2 = new;\n"
      "    repeat (32) begin\n"
      "      void'(s1.randomize());\n"
      "      if (s1.v == s2.v) agree++;\n"
      "      before = s2.v;\n"
      "      void'(s2.randomize());\n"
      "      if (s1.v == s2.v) agree++;\n"
      "      if (s1.v != before) changed++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", agree, changed > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

// 18.6.3: if randomize() fails the random variables retain their previous
// values and post_randomize() is not called: with the ceiling at 0 no x
// lies at or below it and above the inline 0, so the call returns 0, x and
// y keep the values the first call drew, and the counter post_randomize()
// steps stays at that call's 1.
TEST(RandomizationBehaviorRun, AFailedCallRetainsTheValuesWithoutPost) {
  SimFixture f;
  std::string out = RunCapture(
      "class Fallible;\n"
      "  rand bit [7:0] x;\n"
      "  rand bit [7:0] y;\n"
      "  int ceiling = 255;\n"
      "  int post_calls = 0;\n"
      "  constraint bounded { x <= ceiling; }\n"
      "  function void post_randomize();\n"
      "    post_calls++;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok, kept_x, kept_y;\n"
      "  initial begin\n"
      "    Fallible fa = new;\n"
      "    ok = fa.randomize();\n"
      "    kept_x = fa.x;\n"
      "    kept_y = fa.y;\n"
      "    fa.ceiling = 0;\n"
      "    ok = fa.randomize() with { x > 0; };\n"
      "    $display(\"%0d %0d %0d\", ok, fa.x == kept_x && fa.y == kept_y,\n"
      "             fa.post_calls);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 1\n");
}

// 18.6.3: randomize() implements object random stability, an object's RNG
// seeded by srandom(): two Seeded seeded alike draw the same a and b on
// each of 8 calls, and one seeded otherwise draws another pair in some.
TEST(RandomizationBehaviorRun, ObjectsSeededAlikeDrawAlike) {
  SimFixture f;
  std::string out = RunCapture(
      "class Seeded;\n"
      "  rand bit [15:0] a;\n"
      "  rand bit [15:0] b;\n"
      "endclass\n"
      "module t;\n"
      "  int same = 0, differ = 0;\n"
      "  initial begin\n"
      "    Seeded p = new;\n"
      "    Seeded q = new;\n"
      "    Seeded r = new;\n"
      "    p.srandom(7);\n"
      "    q.srandom(7);\n"
      "    r.srandom(8);\n"
      "    repeat (8) begin\n"
      "      void'(p.randomize());\n"
      "      void'(q.randomize());\n"
      "      void'(r.randomize());\n"
      "      if (p.a == q.a && p.b == q.b) same++;\n"
      "      if (p.a != r.a || p.b != r.b) differ++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", same, differ > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 1\n");
}

}  // namespace
