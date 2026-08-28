#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 18.17.6 governs aborting productions with break and return. It owns no
// grammar of its own; break and return are ordinary procedural statements
// (12.8 for break) appearing inside randsequence code blocks. The rules are
// purely about how each statement unwinds sequence generation, so the whole
// subclause lives at the simulator stage (stmt_exec.cpp randsequence engine).

// break forces a jump out of the randsequence block; statements written after
// the randsequence still execute (execution continues at the next statement).
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
  EXPECT_EQ(x, 1u);  // b never generated
  EXPECT_EQ(y, 5u);  // statement after randsequence ran
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
  EXPECT_EQ(x, 2u);  // loop broke at i==3, last write i==2
  EXPECT_EQ(y, 7u);  // production b still generated
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

// break "can appear in any code block", not only a production code block. A
// rule's weight-specification code block (`:= weight { ... }`) is a distinct
// syntactic code-block position; a break there must still terminate the whole
// randsequence, so no production standing after the rule that holds it is
// generated.
//
// §18.17.7 fixes when that block runs relative to the rule's own production
// list: "Only the return values of productions already generated (i.e., to the
// left of the code block accessing them) can be retrieved", and a block written
// after the weight has the whole production list to its left. The clause's own
// LIST example reads ITEM, a value-returning production of the same rule, in
// the block after `:= 8`. So a's list generates p first and the block runs
// after it.
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
  // p generates first (x=5), then a's weight-spec block adds 1 and breaks,
  // unwinding the whole randsequence so b never adds its 9: x == 6. Each block
  // accumulates rather than assigning so that the case observes the order as
  // well as the abort -- an assigning block reads 1 whichever ran first, and a
  // break that aborted only production a would read 15.
  EXPECT_EQ(x, 6u);
}

// return in a weight-specification code block aborts only the current
// production and generation continues with the next production, exactly as
// return does from a production code block. Confirms the abort scope is the
// same across code-block positions.
//
// §18.17.7 puts that block after the rule's production list, as the case above
// quotes, so the list has already generated when the return runs and the return
// skips nothing of it. What the case pins is the abort scope: the randsequence
// carries on with the production following the aborted one.
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
  // a's list generates p (trace 5), then a's weight block appends 1 (51) and
  // returns, ending production a; b still follows -> 51*10+9 = 519. A break
  // there would have unwound the randsequence and left 51.
  EXPECT_EQ(trace, 519u);
}

// 18.17.6: the break terminates the randsequence block and nothing wider. The
// randsequence statement itself finishes normally, so a loop enclosing it runs
// its remaining iterations instead of being terminated in its turn. A break
// that leaked out of the randsequence would satisfy 12.8 against this for loop
// and stop it after one pass.
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
  EXPECT_EQ(x, 6u);   // three passes of a, and b never generated
  EXPECT_EQ(y, 15u);  // the loop body finished all three iterations
}

// 18.17.6: a break in a production code block leaves the randsequence block,
// not the subroutine holding it. The statements written after the randsequence
// in the task body still run, and the caller resumes where the call left off.
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
  EXPECT_EQ(x, 3u);   // b never generated
  EXPECT_EQ(y, 24u);  // the task ran on past the randsequence, then the caller
}

// 18.17.6: a return in a production code block aborts that production and
// nothing wider, so inside a task it is not the task's return. Generation
// continues with the next production, and the task body continues after the
// randsequence.
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
  EXPECT_EQ(x, 33u);  // a aborted before 500, then b still generated
  EXPECT_EQ(y, 24u);  // the task ran on past the randsequence, then the caller
}

// 18.17.6: break "can appear in any code block", which includes the weight
// code block of a rule reached as a rand join operand (18.17.5). Expanding an
// operand runs that rule's weight code, so the break fires there, before any
// interleaving, and terminates the whole randsequence: the other operand and
// the production written after the rand join are never generated.
TEST(RandsequenceSim, BreakInRandJoinWeightCodeTerminatesRandsequence) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  int x;\n"
                                 "  int y;\n"
                                 "  initial begin\n"
                                 "    x = 0;\n"
                                 "    y = 0;\n"
                                 "    randsequence(main)\n"
                                 "      main : j tail;\n"
                                 "      j    : rand join s1 s2;\n"
                                 "      s1   : p := 1 { x = x + 3; break; };\n"
                                 "      p    : { x = x + 900; };\n"
                                 "      s2   : { x = x + 7; };\n"
                                 "      tail : { x = x + 50; };\n"
                                 "    endsequence\n"
                                 "    y = y + 6;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  // Operands are expanded in the order written, so s1's weight code runs first
  // and its break leaves s2 (7), p (900) and tail (50) ungenerated.
  EXPECT_EQ(x, 3u);
  EXPECT_EQ(y, 6u);  // execution resumed after the randsequence
}

// 18.17.6: return aborts only the current production, so a return in the
// weight code of a rand join operand drops that operand's contribution and
// leaves the interleaving intact. The sibling operand still generates, and so
// does the production written after the rand join.
TEST(RandsequenceSim, ReturnInRandJoinWeightCodeAbortsOperandOnly) {
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
  // s1's weight code adds 2 and aborts s1, so p (900) contributes nothing; s2
  // (4) is still interleaved and tail (30) still follows the join. A break
  // there would have left 2, and ignoring the return would have left 936.
  EXPECT_EQ(x, 36u);
}

}  // namespace
