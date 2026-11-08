#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ScopeRandomizeWithRun, TheFirstCallDrawsThreeUnderTwoRelations) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int ok = 0, held = 0, c_moved = 0, prev_c = 0;\n"
      "  task stimulus(int length);\n"
      "    int a, b, c;\n"
      "    ok += std::randomize(a, b, c) with { a < b; a + b < length; };\n"
      "    if (a < b && a + b < length) held++;\n"
      "    if (c != prev_c) c_moved++;\n"
      "    prev_c = c;\n"
      "  endtask\n"
      "  initial begin\n"
      "    repeat (32) stimulus(50);\n"
      "    $display(\"%0d %0d %0d\", ok, held, c_moved > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

TEST(ScopeRandomizeWithRun, TheSecondCallHoldsTheUnnamedLocal) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int ok = 0, held = 0, kept = 0;\n"
      "  task stimulus(int length);\n"
      "    int a, b, c, c_first;\n"
      "    void'(std::randomize(a, b, c) with { a < b; a + b < length; });\n"
      "    c_first = c;\n"
      "    ok += std::randomize(a, b) with { b - a > length; };\n"
      "    if (b - a > length) held++;\n"
      "    if (c == c_first) kept++;\n"
      "  endtask\n"
      "  initial begin\n"
      "    repeat (32) stimulus(50);\n"
      "    $display(\"%0d %0d %0d\", ok, held, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 32\n");
}

TEST(ScopeRandomizeWithRun, ARelationBetweenTwoArgumentsHoldsOverInts) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a, b, ok = 0, held = 0;\n"
      "  initial begin\n"
      "    repeat (32) begin\n"
      "      ok += std::randomize(a, b) with { a < b; };\n"
      "      if (a < b) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(ScopeRandomizeWithRun, ASumBoundAgainstTheStateHoldsOverInts) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a, b, length = 50, ok = 0, held = 0;\n"
      "  initial begin\n"
      "    repeat (32) begin\n"
      "      ok += std::randomize(a, b) with { a + b < length; };\n"
      "      if (a + b < length) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(ScopeRandomizeWithRun, TwoRelationsOverNarrowArgumentsHold) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  int length = 50, ok = 0, held = 0;\n"
      "  initial begin\n"
      "    repeat (32) begin\n"
      "      ok += std::randomize(a, b) with { a < b; a + b < length; };\n"
      "      if (a < b && a + b < length) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(ScopeRandomizeWithRun, TwoRelationsOverTwoIntArgumentsHold) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a, b, length = 50, ok = 0, held = 0;\n"
      "  initial begin\n"
      "    repeat (32) begin\n"
      "      ok += std::randomize(a, b) with { a < b; a + b < length; };\n"
      "      if (a < b && a + b < length) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(ScopeRandomizeRun, APropertyNamedInAMethodIsRandomized) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  int p;\n"
      "  int bad = 0;\n"
      "  function void go(int lim);\n"
      "    int q;\n"
      "    if (std::randomize(p, q) with {\n"
      "          p inside {[lim:lim + 2]}; q == p * 2; } != 1) bad++;\n"
      "    if (!(p >= lim && p <= lim + 2 && q == p * 2)) bad++;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static K k = new;\n"
      "    repeat (10) k.go(40);\n"
      "    $display(\"%0d %0d\", k.bad, k.p >= 40 && k.p <= 42);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

TEST(ScopeRandomizeWithRun, ADisjunctionHoldsBesideARelationOverOneVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit x, y;\n"
      "  int bad = 0, fails = 0;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 200; i++) begin\n"
      "      x = 1; y = 1;\n"
      "      if (std::randomize(x, y) with { (x != 1'b1) || (!y || !y);\n"
      "                                      !y || y || y; } != 1) fails++;\n"
      "      if (x == 1 && y == 1) bad++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", fails, bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0\n");
}

}  // namespace
