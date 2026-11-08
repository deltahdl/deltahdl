#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(ScopeRandomizeRun, NoArgumentListBeforeTheClauseIsTheSameCheck) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  int holds, fails, alone;\n"
      "  initial begin\n"
      "    a = 1; b = 2;\n"
      "    holds = std::randomize with { a < b; };\n"
      "    a = 3;\n"
      "    fails = std::randomize with { a < b; };\n"
      "    alone = std::randomize;\n"
      "    $display(\"%0d %0d %0d %0d\", holds, fails, alone,\n"
      "             a == 3 && b == 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1 1\n");
}

TEST(ScopeRandomizeRun, ABareRandomizeOutsideAClassIsTheNoArgumentCall) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] a = 3;\n"
      "  int ok, in_f;\n"
      "  function int f;\n"
      "    return randomize;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    ok = randomize;\n"
      "    in_f = f();\n"
      "    $display(\"%0d %0d %0d\", ok, in_f, a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 3\n");
}

}  // namespace
