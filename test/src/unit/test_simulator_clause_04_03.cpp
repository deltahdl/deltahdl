#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §4.3 "Event simulation" defines the vocabulary the rest of the scheduling
// model is built on. It is definitional prose -- no BNF, no construct-level
// grammar -- so the rules it OWNS are the meanings of the terms it introduces:
//
//   * update event:     every change in state of a net or variable.
//   * evaluation event: the evaluation of a process; a process sensitive to an
//                       update event is considered for evaluation when that
//                       event is executed.
//
// The discriminating, user-visible consequence of the update-event definition
// is the word "change": a write that leaves a net or variable at its existing
// value is not a change in state, so it is not an update event, so processes
// sensitive to that signal are not re-evaluated. These tests observe that
// definition end to end -- real source, elaboration, lowering, and a run --
// using the sensitivity (`@`) and continuous-assignment constructs of the
// dependency subclauses only as the mechanism that produces the input.
//
// In the simulator, a write always calls Variable::NotifyWatchers, but a
// level-sensitive watcher (awaiters.h CheckEdge with Edge::kNone) only resumes
// its process when prev_value differs from value -- so a same-value write
// produces no evaluation event. That is the production code these tests pin.

namespace {

// §4.3: a genuine change in a variable's state is an update event, so the
// process sensitive to it is evaluated; a same-value write is not a change and
// therefore is not an update event, so the process is not evaluated. The
// counter distinguishes the two: two real transitions but three writes yield a
// count of exactly two.
TEST(EventSimulationSim, SameValueVariableWriteIsNotAnUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  int changes;\n"
      "  initial changes = 0;\n"
      "  always @(a) changes = changes + 1;\n"
      "  initial begin\n"
      "    #1 a = 8'd5;\n"  // x -> 5: state change, update event, evaluated
      "    #1 a = 8'd5;\n"  // 5 -> 5: no change, no update event, not evaluated
      "    #1 a = 8'd9;\n"  // 5 -> 9: state change, update event, evaluated
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* changes = f.ctx.FindVariable("changes");
  ASSERT_NE(changes, nullptr);
  EXPECT_EQ(changes->value.ToUint64(), 2u);
}

// §4.3: when an update event is executed, the process sensitive to it is
// evaluated (an evaluation event), and that evaluation produces the process's
// outputs. Here the change on `a` drives the sensitive block, whose output `b`
// takes on the propagated value.
TEST(EventSimulationSim, VariableStateChangePropagatesToSensitiveProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  always @(a) b = a;\n"
      "  initial begin\n"
      "    a = 8'd0; b = 8'd0;\n"
      "    #1 a = 8'd42;\n"  // change -> update event -> evaluated -> b tracks
                             // a
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

// §4.3 names "net or variable" as the state whose change is an update event, so
// the rule -- including the "change" qualifier -- applies to a net as much as a
// variable. A continuous assignment makes the net `y` follow `a`. Three net
// state changes are genuine update events that evaluate the process watching
// `y`: the time-0 settle from the net's default z to the seeded value 1, and
// the two later transitions 1->7 and 7->9. The repeated same-value write leaves
// `y` at 7, which is not a change and so is not an update event -- it adds no
// evaluation. The count is therefore three; were a same-value net re-drive
// wrongly treated as an update event it would be four.
TEST(EventSimulationSim, NetStateChangeIsAlsoAnUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  wire [7:0] y;\n"
      "  int seen;\n"
      "  assign y = a;\n"
      "  initial seen = 0;\n"
      "  always @(y) seen = seen + 1;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"     // t=0: net y settles z -> 1 (a net state change)
      "    #1 a = 8'd7;\n"  // 1 -> 7: net state change -> update event
      "    #1 a = 8'd7;\n"  // 7 -> 7: no change on y -> no update event
      "    #1 a = 8'd9;\n"  // 7 -> 9: net state change -> update event
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* seen = f.ctx.FindVariable("seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 3u);
}

// §4.3: when an update event is executed, ALL the processes sensitive to that
// event are considered for evaluation -- not just one. Two blocks are made
// sensitive to the same signal `a`; each change of `a` is a single update
// event that must evaluate both, so both independent counters advance on every
// transition. This pins the per-watcher bookkeeping that keeps sibling waiters
// on one signal from starving each other. Two transitions therefore give one
// counter 2 and the other 20.
TEST(EventSimulationSim, AllProcessesSensitiveToAnUpdateEventAreEvaluated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  int c1, c2;\n"
      "  initial begin c1 = 0; c2 = 0; end\n"
      "  always @(a) c1 = c1 + 1;\n"
      "  always @(a) c2 = c2 + 10;\n"
      "  initial begin\n"
      "    #1 a = 8'd4;\n"  // change -> one update event -> both evaluated
      "    #1 a = 8'd9;\n"  // change -> one update event -> both evaluated
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* c1 = f.ctx.FindVariable("c1");
  auto* c2 = f.ctx.FindVariable("c2");
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  EXPECT_EQ(c1->value.ToUint64(), 2u);
  EXPECT_EQ(c2->value.ToUint64(), 20u);
}

// §4.3: an update event evaluates the processes sensitive to THAT event -- not
// every process. Here the only process is sensitive to `b`, while the run only
// ever changes `a`. Those changes on `a` are update events, but the process is
// not sensitive to them, so it is never evaluated and its counter stays zero.
// A simulator that woke processes indiscriminately on any update event would
// leave the counter at two. `b` is never written, so it contributes no event
// of its own, isolating the observation to selectivity.
TEST(EventSimulationSim, ProcessNotSensitiveToTheChangedSignalIsNotEvaluated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int cnt;\n"
      "  initial cnt = 0;\n"
      "  always @(b) cnt = cnt + 1;\n"
      "  initial begin\n"
      "    #1 a = 8'd5;\n"  // update event on a; process watches b, not a
      "    #1 a = 8'd6;\n"  // another update event on a; still not evaluated
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* cnt = f.ctx.FindVariable("cnt");
  ASSERT_NE(cnt, nullptr);
  EXPECT_EQ(cnt->value.ToUint64(), 0u);
}

// §4.3 defines a process as an object that responds to changes on its inputs to
// produce outputs, and lists always_comb among its examples of processes. This
// covers that process form -- one whose sensitivity is implicit rather than a
// written `@` list -- as an input form distinct from the explicit event
// controls above: a change on the read input `in` is an update event that
// evaluates the always_comb process (an evaluation event), whose output `outv`
// then carries the recomputed value.
TEST(EventSimulationSim, AlwaysCombProcessRespondsToAnInputUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] in;\n"
      "  logic [7:0] outv;\n"
      "  always_comb outv = in + 8'd1;\n"
      "  initial begin\n"
      "    in = 8'd10;\n"     // settles outv to 11
      "    #1 in = 8'd20;\n"  // update event on in -> always_comb re-evaluated
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* outv = f.ctx.FindVariable("outv");
  ASSERT_NE(outv, nullptr);
  EXPECT_EQ(outv->value.ToUint64(), 21u);
}

}  // namespace
