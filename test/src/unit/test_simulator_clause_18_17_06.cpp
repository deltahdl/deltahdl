#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 18.17.6 governs aborting productions with break and return. It owns no
// grammar of its own; break and return are ordinary procedural statements
// (12.8 for break) appearing inside randsequence code blocks. The rules are
// purely about how each statement unwinds sequence generation, so the whole
// subclause lives at the simulator stage (stmt_exec.cpp randsequence engine).

uint64_t RunModule(SimFixture& f, const char* src, std::string_view var) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable(var);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : 0;
}

// break terminates the sequence generation: once a break fires in a production
// code block, the productions that would follow are never generated.
TEST(RandsequenceSim, BreakTerminatesRandsequence) {
  SimFixture f;
  uint64_t x = RunModule(f,
                         "module t;\n"
                         "  logic [7:0] x;\n"
                         "  initial begin\n"
                         "    x = 8'd0;\n"
                         "    randsequence(main)\n"
                         "      main : first second;\n"
                         "      first : { x = 8'd10; break; };\n"
                         "      second : { x = 8'd99; };\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "x");
  // second is never generated, so its assignment never runs.
  EXPECT_EQ(x, 10u);
}

// break forces a jump out of the randsequence block; statements written after
// the randsequence still execute (execution continues at the next statement).
TEST(RandsequenceSim, BreakResumesExecutionAfterRandsequence) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 1u);  // b never generated
  EXPECT_EQ(vy->value.ToUint64(), 5u);  // statement after randsequence ran
}

// With no enclosing loop, break unwinds immediately: statements written after
// the break in the same production code block are not executed, and the
// production that would follow is never generated.
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
  // x=1 runs; break exits the block so x=7 never runs and b never generates.
  EXPECT_EQ(x, 1u);
}

// Per 12.8, a break inside a loop statement terminates only the smallest
// enclosing loop, not the randsequence. After the loop ends normally, the
// subsequent production is still generated.
TEST(RandsequenceSim, BreakInsideLoopTerminatesLoopNotRandsequence) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);
  EXPECT_EQ(vx->value.ToUint64(), 2u);  // loop broke at i==3, last write i==2
  EXPECT_EQ(vy->value.ToUint64(), 7u);  // production b still generated
}

// return aborts the current production: the remaining production items of the
// rule containing the return are skipped, but generation continues with the
// next production in the enclosing rule.
TEST(RandsequenceSim, ReturnAbortsCurrentProductionAndContinuesNext) {
  SimFixture f;
  // main : p q r. q is "sub { return; } tail": the return aborts q, so tail is
  // never generated, but r (the production following q in main) still is.
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
  // p=1, q runs sub=2 then return (tail's 8 skipped), then r=3 -> 123.
  EXPECT_EQ(trace, 123u);
}

// return is absorbed at the production it aborts; it does not unwind the whole
// randsequence. A production that always returns can be reached from several
// parents, and each time generation simply moves on to the next production.
TEST(RandsequenceSim, ReturnContinuesWithNextProductionEachInvocation) {
  SimFixture f;
  // bb aborts itself on every generation; cc must still follow it both times bb
  // is reached (once inside p1, once inside p2).
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
  // p1: aa=1, bb aborts (9 skipped), cc=3 -> 13; p2 repeats -> 1313.
  EXPECT_EQ(trace, 1313u);
}

}  // namespace
