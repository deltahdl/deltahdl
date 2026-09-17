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

}  // namespace
