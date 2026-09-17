#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.12: the scope randomize function assigns random values to the
// variables its arguments name in the current scope, addr and data of
// module scope and rd_wr local to the function in the clause's gen_stim,
// and returns 1 where it sets all of them: over 32 calls every call
// succeeds, addr and data move and both values of rd_wr are seen, as the
// design test/src/e2e/scope_randomize.sv runs it.
TEST(ScopeRandomizeRun, TheClausesGenStimSetsEveryNamedVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [15:0] addr;\n"
      "  bit [31:0] data;\n"
      "  int calls = 0, addr_moved = 0, data_moved = 0, reads = 0;\n"
      "  int writes = 0;\n"
      "  bit [15:0] prev_addr;\n"
      "  bit [31:0] prev_data;\n"
      "  function bit gen_stim();\n"
      "    bit success, rd_wr;\n"
      "    success = randomize(addr, data, rd_wr);\n"
      "    calls += success;\n"
      "    return rd_wr;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    repeat (32) begin\n"
      "      prev_addr = addr;\n"
      "      prev_data = data;\n"
      "      if (gen_stim()) reads++; else writes++;\n"
      "      if (addr != prev_addr) addr_moved++;\n"
      "      if (data != prev_data) data_moved++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d %0d\", calls, addr_moved > 0, data_moved > "
      "0,\n"
      "             reads > 0 && writes > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 1 1 1\n");
}

// 18.12: called with no argument, the scope randomize changes no variable
// and checks its constraints, every expression of its constraint_block
// evaluated: 1 with a < b true on the current values and 0 with it false,
// a and b untouched either way.
TEST(ScopeRandomizeRun, NoArgumentEvaluatesTheBlockOnTheCurrentValues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  int holds, fails, kept;\n"
      "  initial begin\n"
      "    a = 1; b = 2;\n"
      "    holds = std::randomize() with { a < b; };\n"
      "    a = 3;\n"
      "    fails = std::randomize() with { a < b; };\n"
      "    kept = a == 3 && b == 2;\n"
      "    $display(\"%0d %0d %0d\", holds, fails, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1\n");
}

// 18.12: the scope randomize returns 0 where it cannot set a random
// variable to a valid value: an 8-bit a required above 300 has no such
// value, so the call returns 0 and a keeps its value.
TEST(ScopeRandomizeRun, AnUnsatisfiableBlockReturnsZeroAndHoldsTheValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] a;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    ok = std::randomize(a) with { a > 300; };\n"
      "    $display(\"%0d %0d\", ok, a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 3\n");
}

}  // namespace
