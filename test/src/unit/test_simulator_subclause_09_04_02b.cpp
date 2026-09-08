// The `b` half of the §9.4.2 event-control family. Where the `a` file reads the
// event control against writes made from an initial or always block, this file
// reads it against writes a subroutine call makes: once from inside a void
// function's body, and once through a function's `output` formal on copy-out.
// §9.4.2 says the event control resumes on a change to the expression however
// that change was produced, so the writer's syntax is what these cases vary.
// The cases from PostfixIncrementWakesAnEventControl on carry the same reading
// to a third writer, the increment and decrement operators, whose store
// notified nobody at all: the bare `i++` statement, the prefix and decrement
// spellings, a for-loop step, and a target held by force, which has to suppress
// the notification along with the store.

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// A void function called with parentheses is the one writer that reaches the
// subroutine-body executor: SetupTaskCall declines it, so ExecFunctionBody runs
// the body and ExecFuncIdentifierAssign performs `x = v`. That path stored the
// value and notified nobody, and because a notification destructively moves the
// watcher vector, the always block parked on `@(x)` never ran again. The two
// calls below are therefore invisible before the fix and the count stops at the
// one wake the initial block's own write produced.
//
// A task body would not read this rule: ExecInlineTaskCall walks the body
// through ExecStmt to AssignToScalarLhs, which already notifies, so the same
// source written with a task passes either way.
TEST(EventControlSim, FunctionBodyWriteWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int woke;\n"
      "  function void poke(input logic [7:0] v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  always @(x) woke = woke + 1;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #1 poke(8'd2);\n"
      "    #1 poke(8'd3);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// The argument copy-out, which is a different route and not a second reading of
// the hole above: #3481 suspected it of the same silence, but
// WritebackOutputArgs hands the value to PerformBlockingAssign, which notifies.
// So this case passes on either side of the fix and stands as a guard on the
// route the issue questioned, pinning it beside the body write. The middle call
// writes the value already held, which the awaiter's own change gate drops, so
// a copy-out that notified unconditionally would read 3 here rather than 2.
TEST(EventControlSim, OutputFormalCopyOutWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] y;\n"
      "  int seen;\n"
      "  function void fill(output logic [7:0] o, input logic [7:0] v);\n"
      "    o = v;\n"
      "  endfunction\n"
      "  always @(y) seen = seen + 1;\n"
      "  initial begin\n"
      "    fill(y, 8'd9);\n"
      "    #1 fill(y, 8'd9);\n"
      "    #1 fill(y, 8'd4);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// The increment operators are the third writer, and the one §9.4.2 covers by
// the same sentence as the other two: WriteIncDecTarget stored the new value
// and told nobody, so `i++` in an ordinary process body changed the variable
// without waking anything parked on it. A bare `i++;` is a kExprStmt, which
// ExecStmt hands to ExecInlineTaskCall, whose non-call fall-through evaluates
// the expression -- so this is the plainest statement form there is, and it was
// the one form of write that left an awaiter parked for the rest of the run.
// Both increments below were therefore invisible and the count stopped at 0.
TEST(EventControlSim, PostfixIncrementWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  int hits;\n"
      "  always @(i) hits = hits + 1;\n"
      "  initial begin\n"
      "    #1 i++;\n"
      "    #1 i++;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// EvalPrefixUnary and EvalPostfixUnary are separate entry points that meet only
// inside EvalIncDec, and the decrement differs from the increment in the token
// each tests for, so the case above reaches one of the two doors and one of the
// two tokens. This walks the other three spellings through one process: `++w`
// and `--w` come in by the prefix door, `w--` by the postfix door with the
// minus token. The opening `w = 4'd7` is an ordinary blocking assignment, which
// notified all along, so it is the wake a broken build still counts: 1 here
// rather than 4 says the store landed and the notification did not, and it is
// what separates that from a build that never woke the block at all. The value
// of w is read as well because a notification that fired without the store
// having moved the variable would satisfy the count alone.
TEST(EventControlSim, PrefixAndDecrementSpellingsWakeAnEventControl) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] w;\n"
      "  int n;\n"
      "  always @(w) begin\n"
      "    n = n + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    w = 4'd7;\n"
      "    #1 ++w;\n"
      "    #1 --w;\n"
      "    #1 w--;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 4u);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.ToUint64(), 6u);
}

// A for-loop step is the second route into the same store: ExecFor runs each
// step through ExecStmt rather than as a statement of the body, so the loop
// below reaches WriteIncDecTarget without ever writing k with an `=` after the
// initialization. That initialization is the discriminating one. `k = 1` moves
// k off 0 and notifies the way any blocking assignment does, so a build in
// which the step notifies nobody still counts one wake; the three steps are
// what carry the count from 1 to 4. The leading `#1` puts the loop after the
// always block has parked, and the body's `#1` gives the woken block a chance
// to run between one step and the next, so the four wakes are four separate
// resumptions rather than a single collapsed one.
TEST(EventControlSim, ForStepIncrementWakesAnEventControl) {
  SimFixture f;
  auto* taps = RunAndFindVar(
      "module t;\n"
      "  int k;\n"
      "  int taps;\n"
      "  always @(k) taps = taps + 1;\n"
      "  initial begin\n"
      "    #1;\n"
      "    for (k = 1; k < 4; k++) #1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "taps");
  ASSERT_NE(taps, nullptr);
  EXPECT_EQ(taps->value.ToUint64(), 4u);
  auto* k = f.ctx.FindVariable("k");
  ASSERT_NE(k, nullptr);
  EXPECT_EQ(k->value.ToUint64(), 4u);
}

// §10.6.2: a force "shall override a procedural assignment ... until a release
// procedural statement is executed on the variable", so an increment under a
// force stores nothing -- and a change nobody made is not a change §9.4.2 asks
// anyone to detect. That is why the notification belongs inside the is_forced
// gate and not after it, and this case is what holds it there: p stays at the
// forced 5 across two increments, and the process parked on @(p) is still
// parked when the run ends. The awaiter is armed at time 1, after the force at
// time 0, so the force's own effect on p cannot be what leaves fired at 0; only
// the two increments at times 2 and 3 are being watched. Unlike the three cases
// above this one reads the same values before the fix and after it. It is not a
// test of the missing notification but of where the notification was put: it
// fails only for a build that notifies outside the gate, which would set fired
// to 1 while p still read 5.
TEST(EventControlSim, ForcedTargetIncrementWakesNoEventControl) {
  SimFixture f;
  auto* fired = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] p;\n"
      "  int fired;\n"
      "  initial begin\n"
      "    force p = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    #1;\n"
      "    @(p) fired = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 p++;\n"
      "    #1 p++;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "fired");
  ASSERT_NE(fired, nullptr);
  EXPECT_EQ(fired->value.ToUint64(), 0u);
  auto* p = f.ctx.FindVariable("p");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_forced);
  EXPECT_EQ(p->value.ToUint64(), 5u);
}

}  // namespace
