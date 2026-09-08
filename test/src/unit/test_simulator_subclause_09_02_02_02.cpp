#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombLowering, AlwaysCombRetrigger) {
  LowerFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 6u);
}

TEST(AlwaysCombLowering, AlwaysCombAutoTriggerTimeZero) {
  LowerFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] b;\n"
      "  always_comb b = 42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

TEST(AlwaysCombSim, ConcurrentAlwaysCombBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, r1, r2;\n"
      "  initial a = 8'd10;\n"
      "  always_comb r1 = a + 8'd1;\n"
      "  always_comb r2 = a + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 12u);
}

TEST(AlwaysCombSim, AlwaysCombWithBeginEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, r1, r2;\n"
      "  initial a = 8'd5;\n"
      "  always_comb begin\n"
      "    r1 = a + 8'd1;\n"
      "    r2 = a + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 7u);
}

TEST(AlwaysCombSim, AlwaysCombTriggersAfterInitial) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd99;\n"
      "  always_comb b = a;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 99u);
}

TEST(AlwaysCombSim, AlwaysCombRetriggersOnChange) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a = 8'd10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 11u);
}

// Elaborates, lowers and runs `src` -- a design whose one always_comb copies
// `a` into `b` and increments `runs` -- then asserts the procedure evaluated
// exactly `expected_runs` times. The count is the whole observation: what
// separates a select write that stored a bit from one that stored nothing is
// whether the inferred sensitivity list saw an event, and `b` alone cannot
// tell those apart, because a write that stores nothing leaves `b` holding the
// value the previous evaluation already gave it.
void ExpectAlwaysCombRunCount(const char* src, uint64_t expected_runs) {
  SimFixture f;
  auto* runs = RunAndFindVar(src, f, "runs");
  ASSERT_NE(runs, nullptr);
  EXPECT_EQ(runs->value.ToUint64(), expected_runs);
}

TEST(AlwaysCombSim,
     AlwaysCombDoesNotRetriggerWhenAnOutOfBoundsBitSelectWriteChangesNothing) {
  // §11.5.1 (printed page 296) says a bit-select address outside the vector's
  // range "shall have no effect on the data stored when written", and §9.4.2
  // (printed page 232) says "a change of value in any operand of the expression
  // without a change in the result of the expression shall not be detected as
  // an event". §9.2.2.2 (printed page 222) gives an always_comb "an inferred
  // sensitivity list", which is the list §9.4.2 governs. So the write of a[9]
  // to an 8-bit `a` stores no bit and owes the procedure no event.
  //
  // Why the count is 2 rather than 3 or 1. The inferred list is {a} alone:
  // exception (b) of §9.2.2.2.1 leaves out "any expression that is also written
  // within the block", which here is `b` and `runs`, and InferSensitivity is
  // called with exclude_written true for an always_comb.
  // Lowerer::LowerProcesses lowers the non-initial processes ahead of the
  // initial ones, so at time zero the always_comb evaluates first (`runs` 1)
  // and arms its watcher while `a` is still 8'hxx; the initial block then
  // writes 8'd0, a genuine change of the one listed expression, and `runs`
  // reaches 2. At time 1 the out-of-bounds write stores nothing and the count
  // must stay at 2.
  //
  // Reading 3 is the defect. A select write that returned having written
  // nothing still notified the variable's watchers, and the AnyChangeAwaiter an
  // always_comb waits on compares no baseline and resumes on any notify at all.
  // @(a), always @*, $monitor and a clocking block each hold a baseline of
  // their own and stay quiet on a notify that moved nothing, which is why
  // always_comb is the construct that makes this observable.
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a[9] = 1'b1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      2);
}

TEST(AlwaysCombSim,
     AlwaysCombRetriggersWhenAnInBoundsBitSelectWriteChangesTheVector) {
  // The design above with its one index moved from the out-of-range 9 to the
  // in-range 3, and the expected count moved with it. This is what stops the
  // case above from being satisfied by never notifying from a select write at
  // all: an in-bounds a[3] write does change the vector, §9.4.2 (printed page
  // 232) therefore makes it an event on the inferred sensitivity list of
  // §9.2.2.2 (printed page 222), and the always_comb must evaluate a third
  // time. Suppressing the notify for every select write would leave `runs` at 2
  // here while passing the other half of the pair -- the regression the
  // neighbouring arm of this code needed a fix of its own to undo. The two
  // cases differ only in the index, so the counts have to differ with it or
  // neither is discriminating.
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a[3] = 1'b1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      3);
}

TEST(AlwaysCombSim,
     AlwaysCombDoesNotRetriggerWhenAWriteDepositsTheValueTheVariableHolds) {
  // §9.4.2 (printed page 232, last line of the clause) says "a change of value
  // in any operand of the expression without a change in the result of the
  // expression shall not be detected as an event", and §9.2.2.2 (printed page
  // 222) gives an always_comb "an inferred sensitivity list that includes the
  // expressions defined in 9.2.2.2.1" -- the list §9.4.2 governs. A store that
  // deposits the bits the variable already holds changes no result, so it owes
  // the procedure no event, however genuinely the store itself happened.
  //
  // Why the count is 2 rather than 3 or 1. The inferred list is {a} alone:
  // exception (b) of §9.2.2.2.1 leaves out "any expression that is also written
  // within the block", which here is `b` and `runs`, and InferSensitivity is
  // called with exclude_written true for an always_comb.
  // Lowerer::LowerProcesses lowers the non-initial processes ahead of the
  // initial ones, so at time zero the always_comb evaluates first (`runs` 1)
  // and arms its watcher while `a` is still 8'hxx; the initial block then
  // writes 8'd5, a genuine change of the one listed expression, and `runs`
  // reaches 2. At time 1 the second write of 8'd5 changes nothing and the count
  // must stay at 2.
  //
  // Reading 3 is the defect. The write takes ApplyGenericBlockingAssign's
  // fall-through into AssignToScalarLhs, which stores the identical bits and
  // notifies the variable's watchers regardless, and the AnyChangeAwaiter an
  // always_comb waits on captures a baseline it never reads back -- every guard
  // in its body is about frame or process liveness, or a sibling having
  // consumed the suspension -- so any notify at all resumes the process.
  //
  // The same design written `always @(a) runs = runs + 1;` ends at 2 today,
  // because that path is EventAwaiter::CheckEdge, which compares its baseline
  // word by word. One clause, one write, two answers from two awaiters: that
  // divergence is what this case pins.
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #1 a = 8'd5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      2);
}

TEST(AlwaysCombSim, AlwaysCombRetriggersWhenAWriteChangesTheVariable) {
  // The design above with the value written at time 1 moved from 8'd5 to 8'd7,
  // and the expected count moved with it. This is what stops the case above
  // from being satisfied by dropping the notify from the writers altogether:
  // 8'd7 does change `a`, §9.4.2 (printed page 232) therefore makes it an event
  // on the inferred sensitivity list of §9.2.2.2 (printed page 222), and the
  // always_comb must evaluate a third time. A writer that stopped notifying
  // would leave `runs` at 2 here while passing the other half of the pair --
  // exactly the regression a neighbouring arm of this code needed a fix of its
  // own to undo. The two programs differ only in the value written, so the
  // counts have to differ with them or neither case is discriminating.
  ExpectAlwaysCombRunCount(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int runs;\n"
      "  always_comb begin\n"
      "    b = a;\n"
      "    runs = runs + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #1 a = 8'd7;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      3);
}

TEST(AlwaysCombSim, AlwaysCombMuxPattern) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 22u);
}

TEST(AlwaysCombBasicSim, AlwaysCombResultWidth8) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd5;\n"
      "  always_comb begin\n"
      "    result = a;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(AlwaysCombSim, AlwaysCombNonblockingIntraDelay) {
  // §9.2.2.2 shows `d <= #1ns b & c;` as a legal always_comb body: the
  // combinational procedure may use a nonblocking assignment carrying an
  // intra-assignment delay. Drive b and c from an initial block, let the
  // inferred sensitivity retrigger the procedure, and observe that the
  // nonblocking update lands the ANDed value after the delay.
  SimFixture f;
  auto* d = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, d;\n"
      "  always_comb d <= #1 b & c;\n"
      "  initial begin\n"
      "    b = 8'hF0;\n"
      "    c = 8'h3C;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 0x30u);
}

TEST(AlwaysCombSim, AlwaysCombChainedDependency) {
  SimFixture f;
  auto* c = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  always_comb b = a + 8'd1;\n"
      "  always_comb c = b + 8'd1;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    #1 a = 8'd10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 12u);
}

// §9.2.2.2 (printed page 222) gives an always_comb "an inferred sensitivity
// list that includes the expressions defined in 9.2.2.2.1", and §9.4.2
// (printed page 232) makes an event out of "any change in the value of the
// expression" on such a list. §11.4.2 states the increment and decrement
// operators as blocking assignments, so a bare `i++;` in a process body is a
// change of `i` exactly as `i = i + 1;` would be, and the combinational
// procedure reading `i` owes an evaluation to it.
//
// The route is the ordinary process body, not a subroutine's: `i++;` is a
// kExprStmt that ExecStmt hands to ExecInlineTaskCall, whose non-call
// fall-through evaluates it as an expression, reaching EvalIncDec and its store
// to var->value. That store told the variable's watchers nothing, and the
// watcher is the whole mechanism: DropUnwatchableNames keeps every name
// ctx.FindVariable resolves, so this always_comb does hold a live watcher on
// `i` and is waiting on precisely the notification the increment withheld.
// This is the AnyChangeAwaiter arm of the same omission the wait statement
// meets through ExecWait.
//
// The values separate the two answers the run can give. An always_comb
// evaluates once at time zero whatever happens, there with `i` at its 2-state
// default of 0 (§6.8, Table 6-7), so `y` is 8'd1; the initial block's write of
// 7 is an ordinary assignment and retriggers the procedure, so `y` is 8'd8
// before the increment ever runs. Only an evaluation caused by the increment
// itself puts 8'd9 in `y`. A procedure that ran only its earlier times leaves
// 8'd8, which is why the assertion is not merely "y moved off its default".
TEST(AlwaysCombSim, AlwaysCombRetriggersOnAnIncrementOperatorWrite) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  logic [7:0] y;\n"
      "  always_comb y = i + 8'd1;\n"
      "  initial begin\n"
      "    i = 7;\n"
      "    #1 i++;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
}

}  // namespace
