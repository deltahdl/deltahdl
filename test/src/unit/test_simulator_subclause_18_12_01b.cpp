#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.12.1: the clause's first call, std::randomize(a, b, c) with a below b
// and their sum below the task argument length: the three arguments are
// the random variables and length a state variable, so over 32 calls of
// stimulus(50) every call succeeds with a < b and a + b < 50, and c is
// drawn though no constraint names it, as the design
// test/src/e2e/scope_randomize_with.sv runs it.
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

// 18.12.1: the clause's second call, std::randomize(a, b) with their
// difference above length: a and b are the random variables and c, no
// argument of it, a state variable, so b - a exceeds 50 on every call and
// c keeps the value the first call gave it.
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

// 18.12.1: a relation between two arguments alone, a below b over whole
// ints, holds on every one of 32 calls.
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

// 18.12.1: a sum of two arguments bounded by the state length alone, over
// whole ints, holds on every one of 32 calls.
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

// 18.12.1: the clause's two relations over 8-bit arguments hold on every
// one of 32 calls.
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

// 18.12.1: the clause's two relations over whole ints, the two arguments
// they name alone, hold on every one of 32 calls.
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

// §18.12.1: inside a class method the scope randomize may name a property of
// the object, bare, beside a local, and its block may read the method's
// formal: p is drawn within lim to lim + 2 and q is twice it.
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

}  // namespace
