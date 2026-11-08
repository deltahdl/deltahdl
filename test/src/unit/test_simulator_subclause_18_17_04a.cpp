#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, RepeatProduction) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  logic [7:0] x;\n"
                         "  initial begin\n"
                         "    x = 8'd0;\n"
                         "    randsequence(main)\n"
                         "      main : repeat(3) inc;\n"
                         "      inc : { x = x + 8'd1; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 3u);
}

TEST(RandsequenceSim, RepeatZeroCountGeneratesNothing) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  int x;\n"
                         "  initial begin\n"
                         "    x = 0;\n"
                         "    randsequence(main)\n"
                         "      main : pre repeated post;\n"
                         "      pre      : { x = 1; };\n"
                         "      repeated : repeat(0) bump;\n"
                         "      bump     : { x = x + 100; };\n"
                         "      post     : { x = x + 10; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 11u);
}

TEST(RandsequenceSim, RepeatCountFromExpression) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  int x;\n"
                         "  int n;\n"
                         "  initial begin\n"
                         "    x = 0;\n"
                         "    n = 4;\n"
                         "    randsequence(main)\n"
                         "      main : repeat(n + 1) inc;\n"
                         "      inc  : { x = x + 1; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 5u);
}

TEST(RandsequenceSim, RepeatCountFromParameter) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  parameter P = 3;\n"
                         "  int x;\n"
                         "  initial begin\n"
                         "    x = 0;\n"
                         "    randsequence(main)\n"
                         "      main : repeat(P) inc;\n"
                         "      inc  : { x = x + 1; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 3u);
}

TEST(RandsequenceSim, RepeatCountFromLocalparam) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  localparam L = 4;\n"
                         "  int x;\n"
                         "  initial begin\n"
                         "    x = 0;\n"
                         "    randsequence(main)\n"
                         "      main : repeat(L) inc;\n"
                         "      inc  : { x = x + 1; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  EXPECT_EQ(x, 4u);
}

TEST(RandsequenceSim, RepeatBreakTerminatesEntireRandsequence) {
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
                       "      main   : looped after;\n"
                       "      looped : repeat(3) body;\n"
                       "      body   : { x = x + 1; if (x == 2) break; };\n"
                       "      after  : { y = 5; };\n"
                       "    endsequence\n"
                       "  end\n"
                       "endmodule\n",
                       "x", "y");
  EXPECT_EQ(x, 2u);
  EXPECT_EQ(y, 0u);
}

}  // namespace
