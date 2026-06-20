#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 18.17.4 governs the repeat production statement. Its grammar (rs_repeat) is
// part of the parent randsequence syntax (Syntax 18-13), so parser acceptance
// belongs to 18.17. What this subclause defines is purely a generation-time
// rule: the repeat expression yields a non-negative integral count, and the
// associated production is generated that many times. The repeat statement
// cannot be aborted partway through -- a break unwinds the whole randsequence
// (the break machinery itself is owned by 18.17.6). All of that is observed at
// the simulator stage in the randsequence engine (stmt_exec.cpp).

// The count specifies exactly how many times the production is generated: a
// fixed count of 3 generates the inc production three times.
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

// A count of zero is a valid non-negative count: the production is generated
// zero times, so its side effects never occur.
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
  // pre sets 1, the repeated production runs bump zero times, post adds 10.
  EXPECT_EQ(x, 11u);
}

// The repeat count is an arbitrary expression, evaluated when the production is
// generated, not just a constant literal.
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
  // n + 1 == 5 generations of inc.
  EXPECT_EQ(x, 5u);
}

// The repeat production statement cannot be terminated prematurely: a break in
// the repeated production does not just stop the loop, it unwinds the entire
// randsequence block. Productions following the repeat are never generated.
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
  // body runs twice (x->1, x->2) then breaks before the third iteration; the
  // break terminates the whole randsequence, so after never generates (y stays
  // 0).
  EXPECT_EQ(x, 2u);
  EXPECT_EQ(y, 0u);
}

}  // namespace
