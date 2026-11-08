#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, BreakResumesExecutionAfterRandsequence) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  logic [7:0] x;\n"
                                 "  logic [7:0] y;\n"
                                 "  initial begin\n"
                                 "    x = 8'd0;\n"
                                 "    y = 8'd0;\n"
                                 "    randsequence(main)\n"
                                 "      main : a b;\n"
                                 "      a : { x = 8'd1; break; };\n"
                                 "      b : { x = 8'd2; };\n"
                                 "    endsequence\n"
                                 "    y = 8'd5;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  EXPECT_EQ(x, 1u);
  EXPECT_EQ(y, 5u);
}

TEST(RandsequenceSim, BreakSkipsRemainingStatementsInSameCodeBlock) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  int x;\n"
                         "  initial begin\n"
                         "    x = 0;\n"
                         "    randsequence(main)\n"
                         "      main : a b;\n"
                         "      a : { x = 1; break; x = 7; };\n"
                         "      b : { x = 9; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 1u);
}

TEST(RandsequenceSim, BreakInsideLoopTerminatesLoopNotRandsequence) {
  SimFixture f;
  auto [x, y] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int x;\n"
                       "  int y;\n"
                       "  initial begin\n"
                       "    x = 0;\n"
                       "    y = 0;\n"
                       "    randsequence(main)\n"
                       "      main : a b;\n"
                       "      a : { for (int i = 0; i < 10; i++) begin\n"
                       "              if (i == 3) break;\n"
                       "              x = i;\n"
                       "            end };\n"
                       "      b : { y = 7; };\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "x", "y");
  EXPECT_EQ(x, 2u);
  EXPECT_EQ(y, 7u);
}

TEST(RandsequenceSim, ReturnAbortsCurrentProductionAndContinuesNext) {
  SimFixture f;
  uint64_t trace = RunModule(f,
                             "module t;\n"
                             "  int trace;\n"
                             "  initial begin\n"
                             "    trace = 0;\n"
                             "    randsequence(main)\n"
                             "      main : p q r;\n"
                             "      p   : { trace = trace * 10 + 1; };\n"
                             "      q   : sub { return; } tail;\n"
                             "      sub : { trace = trace * 10 + 2; };\n"
                             "      tail: { trace = trace * 10 + 8; };\n"
                             "      r   : { trace = trace * 10 + 3; };\n"
                             "    endsequence\n"
                             "  end\n"
                             "endmodule\n",
                             "trace");
  EXPECT_EQ(trace, 123u);
}

TEST(RandsequenceSim, ReturnContinuesWithNextProductionEachInvocation) {
  SimFixture f;
  uint64_t trace = RunModule(f,
                             "module t;\n"
                             "  int trace;\n"
                             "  initial begin\n"
                             "    trace = 0;\n"
                             "    randsequence(main)\n"
                             "      main : p1 p2;\n"
                             "      p1 : aa bb cc;\n"
                             "      p2 : aa bb cc;\n"
                             "      aa : { trace = trace * 10 + 1; };\n"
                             "      bb : { return; trace = trace * 10 + 9; };\n"
                             "      cc : { trace = trace * 10 + 3; };\n"
                             "    endsequence\n"
                             "  end\n"
                             "endmodule\n",
                             "trace");
  EXPECT_EQ(trace, 1313u);
}

TEST(RandsequenceSim, BreakInWeightSpecCodeBlockTerminatesRandsequence) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  logic [7:0] x;\n"
                         "  initial begin\n"
                         "    x = 8'd0;\n"
                         "    randsequence(main)\n"
                         "      main : a b;\n"
                         "      a : p := 1 { x = x + 8'd1; break; };\n"
                         "      p : { x = x + 8'd5; };\n"
                         "      b : { x = x + 8'd9; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 6u);
}

TEST(RandsequenceSim, ReturnInWeightSpecCodeBlockAbortsCurrentProductionOnly) {
  SimFixture f;
  uint64_t trace = RunModule(f,
                             "module t;\n"
                             "  int trace;\n"
                             "  initial begin\n"
                             "    trace = 0;\n"
                             "    randsequence(main)\n"
                             "      main : a b;\n"
                             "      a : p := 1 { trace = trace*10 + 1;"
                             " return; };\n"
                             "      p : { trace = trace*10 + 5; };\n"
                             "      b : { trace = trace*10 + 9; };\n"
                             "    endsequence\n"
                             "  end\n"
                             "endmodule\n",
                             "trace");
  EXPECT_EQ(trace, 519u);
}

TEST(RandsequenceSim, BreakDoesNotTerminateLoopEnclosingRandsequence) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  int x;\n"
                                 "  int y;\n"
                                 "  initial begin\n"
                                 "    x = 0;\n"
                                 "    y = 0;\n"
                                 "    for (int i = 0; i < 3; i++) begin\n"
                                 "      randsequence(main)\n"
                                 "        main : a b;\n"
                                 "        a : { x = x + 2; break; };\n"
                                 "        b : { x = x + 90; };\n"
                                 "      endsequence\n"
                                 "      y = y + 5;\n"
                                 "    end\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  EXPECT_EQ(x, 6u);
  EXPECT_EQ(y, 15u);
}

TEST(RandsequenceSim, BreakInTaskDoesNotReturnFromTask) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  int x;\n"
                                 "  int y;\n"
                                 "  task automatic run;\n"
                                 "    randsequence(main)\n"
                                 "      main : a b;\n"
                                 "      a : { x = x + 3; break; };\n"
                                 "      b : { x = x + 90; };\n"
                                 "    endsequence\n"
                                 "    y = y + 4;\n"
                                 "  endtask\n"
                                 "  initial begin\n"
                                 "    x = 0;\n"
                                 "    y = 0;\n"
                                 "    run;\n"
                                 "    y = y + 20;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  EXPECT_EQ(x, 3u);
  EXPECT_EQ(y, 24u);
}

TEST(RandsequenceSim, ReturnInTaskDoesNotReturnFromTask) {
  SimFixture f;
  auto [x, y] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  int x;\n"
                       "  int y;\n"
                       "  task automatic run;\n"
                       "    randsequence(main)\n"
                       "      main : a b;\n"
                       "      a : { x = x + 3; return; x = x + 500; };\n"
                       "      b : { x = x + 30; };\n"
                       "    endsequence\n"
                       "    y = y + 4;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    x = 0;\n"
                       "    y = 0;\n"
                       "    run;\n"
                       "    y = y + 20;\n"
                       "  end\n"
                       "endmodule\n",
                       "x", "y");
  EXPECT_EQ(x, 33u);
  EXPECT_EQ(y, 24u);
}

TEST(RandsequenceSim, BreakInRandJoinWeightCodeTerminatesRandsequence) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  int x;\n"
                                 "  int y;\n"
                                 "  int z;\n"
                                 "  initial begin\n"
                                 "    x = 0;\n"
                                 "    y = 0;\n"
                                 "    z = 0;\n"
                                 "    randsequence(main)\n"
                                 "      main : j tail;\n"
                                 "      j    : rand join s1 s2;\n"
                                 "      s1   : p := 1 { x = x + 3; break; };\n"
                                 "      p    : { x = x + 900; };\n"
                                 "      s2   : { z = z + 7; };\n"
                                 "      tail : { x = x + 50; };\n"
                                 "    endsequence\n"
                                 "    y = y + 6;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  EXPECT_EQ(x, 903u);
  EXPECT_EQ(y, 6u);
}

TEST(RandsequenceSim, ReturnInRandJoinWeightCodeIsAbsorbedOnceItHasGenerated) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  int x;\n"
                         "  initial begin\n"
                         "    x = 0;\n"
                         "    randsequence(main)\n"
                         "      main : j tail;\n"
                         "      j    : rand join s1 s2;\n"
                         "      s1   : p := 1 { x = x + 2; return; };\n"
                         "      p    : { x = x + 900; };\n"
                         "      s2   : { x = x + 4; };\n"
                         "      tail : { x = x + 30; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 936u);
}

}  // namespace
