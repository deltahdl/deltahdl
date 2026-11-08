#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(RandomizationBehaviorRun, AMembersFailureLeavesTheObjectAsItWas) {
  EXPECT_EQ(RunRootAndLeaf("    r.leaf.ceiling = 0;\n"), "0 0 0 0 0\n");
}

TEST(RandomizationBehaviorRun, AnObjectsFailureLeavesItsMembersAsTheyWere) {
  EXPECT_EQ(RunRootAndLeaf("    r.ceiling = 0;\n"), "0 0 0 0 0\n");
}

}  // namespace
