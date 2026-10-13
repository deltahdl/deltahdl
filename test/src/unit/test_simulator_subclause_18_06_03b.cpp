#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A Root holding a rand Leaf, each kept above 10 and at or below a ceiling
// a test can drop to make it infeasible, and each counting its
// post_randomize() calls.
const char* const kRootAndLeaf =
    "class Leaf;\n"
    "  rand bit [7:0] y;\n"
    "  int ceiling = 255;\n"
    "  int post_calls = 0;\n"
    "  constraint c { y > 10; y <= ceiling; }\n"
    "  function void post_randomize(); post_calls++; endfunction\n"
    "endclass\n"
    "class Root;\n"
    "  rand bit [7:0] x;\n"
    "  rand Leaf leaf;\n"
    "  int ceiling = 255;\n"
    "  int post_calls = 0;\n"
    "  constraint c { x > 10; x <= ceiling; }\n"
    "  function void post_randomize(); post_calls++; endfunction\n"
    "endclass\n";

// Runs `body` on a Root r holding a Leaf, both at 0, and displays the call's
// result, then r.x, r.leaf.y and both post_randomize() counts.
std::string RunRootAndLeaf(const std::string& body) {
  SimFixture f;
  return RunCapture(std::string(kRootAndLeaf) +
                        "module t;\n"
                        "  int ok;\n"
                        "  initial begin\n"
                        "    static Root r = new;\n"
                        "    r.leaf = new;\n" +
                        body +
                        "    ok = r.randomize() with (x) { x < 50; };\n"
                        "    $display(\"%0d %0d %0d %0d %0d\", ok, r.x, "
                        "r.leaf.y, r.post_calls,\n"
                        "             r.leaf.post_calls);\n"
                        "  end\n"
                        "endmodule\n",
                    f);
}

// 18.6.3: a static random variable has one copy for the whole class, so each
// randomize() call changes it for every instance: over 32 rounds of a call on
// each of two Shared, both read the same v after every call, and a call on the
// second changes what the first reads in some round, as the design
// test/src/e2e/randomization_behavior.sv runs it.
TEST(RandomizationBehaviorRun, AStaticVariableChangesInEveryInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "class Shared;\n"
      "  static rand bit [7:0] v;\n"
      "  rand bit [7:0] own;\n"
      "endclass\n"
      "module t;\n"
      "  int agree = 0, changed = 0, previous;\n"
      "  initial begin\n"
      "    static Shared s1 = new;\n"
      "    static Shared s2 = new;\n"
      "    repeat (32) begin\n"
      "      void'(s1.randomize());\n"
      "      if (s1.v == s2.v) agree++;\n"
      "      previous = s2.v;\n"
      "      void'(s2.randomize());\n"
      "      if (s1.v == s2.v) agree++;\n"
      "      if (s1.v != previous) changed++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", agree, changed > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

// 18.6.3: a failed randomize() leaves every random variable at its old value
// and skips post_randomize(): with the ceiling at 0 no x lies at or below it
// and above the inline 0, so the call returns 0, x and y keep the values the
// first call drew, and the counter post_randomize() steps stays at that call's
// 1.
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
      "    static Fallible fa = new;\n"
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
      "    static Seeded p = new;\n"
      "    static Seeded q = new;\n"
      "    static Seeded r = new;\n"
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

// §18.6.3: a randomize() that fails leaves every random variable as it was
// and calls no post_randomize(), its random object members' failure being
// its own: the Leaf held at or below 0 cannot be solved, so the Root keeps
// its x at 0 and neither post_randomize() runs, on the restricted with (x)
// form as on the plain one.
TEST(RandomizationBehaviorRun, AMembersFailureLeavesTheObjectAsItWas) {
  EXPECT_EQ(RunRootAndLeaf("    r.leaf.ceiling = 0;\n"), "0 0 0 0 0\n");
}

// §18.6.3: likewise the Root held at or below 0 cannot be solved, so its
// Leaf keeps its y at 0 and neither post_randomize() runs.
TEST(RandomizationBehaviorRun, AnObjectsFailureLeavesItsMembersAsTheyWere) {
  EXPECT_EQ(RunRootAndLeaf("    r.ceiling = 0;\n"), "0 0 0 0 0\n");
}

}  // namespace
