#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, PassActionBlockInvoked) {
  SvaFixture f;
  bool pass_called = false;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&pass_called]() { pass_called = true; };
  da.fail_action = [&fail_called]() { fail_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(pass_called);
  EXPECT_FALSE(fail_called);
}

TEST(SvaEngine, FailActionBlockInvoked) {
  SvaFixture f;
  bool pass_called = false;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 0;
  da.pass_action = [&pass_called]() { pass_called = true; };
  da.fail_action = [&fail_called]() { fail_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_FALSE(pass_called);
  EXPECT_TRUE(fail_called);
}

TEST(SvaEngine, NoActionBlockDoesNotCrash) {
  DeferredAssertion da;
  da.condition_val = 0;

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(true);
}

TEST(SvaEngine, DeferredAssertionScheduledInObserved) {
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});

  f.scheduler.Run();
  EXPECT_TRUE(executed);
}

TEST(SvaEngine, DeferredAssertionFailsInObserved) {
  SvaFixture f;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 0;
  da.fail_action = [&fail_called]() { fail_called = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(fail_called);
}

TEST(SvaEngine, MultipleDeferredAssertionsQueued) {
  SvaFixture f;
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.pass_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 5);
}

TEST(SvaEngine, EngineDefaultState) {
  SvaEngine engine;
  EXPECT_EQ(engine.DeferredQueueSize(), 0u);
}

TEST(SvaEngine, FlushClearsQueue) {
  SvaFixture f;

  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueueDeferredAssertion(da);
  EXPECT_EQ(f.engine.DeferredQueueSize(), 1u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);
}

// §16.4 P7: "the reporting or action blocks are scheduled at a later point
// in the current time step." This test puts a non-deferred assignment AFTER
// a deferred-assertion pass action that writes the same variable. If the
// deferred action ran inline (the §16.3 simple-immediate behavior) the
// inline assignment would overwrite the post-statement assignment, leaving
// the variable at 99. The §16.4 deferral routes the action into a later
// region (Reactive for #0), so the deferred write lands AFTER the inline
// write and the variable settles at 44.
TEST(AssertionStatementSim, ObservedDeferredActionFiresAfterFollowingStmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (1) x = 8'd44;\n"
      "    x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// §16.4 P14: "For a final deferred assertion, the subroutine shall be
// scheduled in the Postponed region." The Postponed region runs after the
// active/reactive regions, so a final-deferred pass action sequenced
// before a same-variable non-deferred assignment must still observably
// land last.
TEST(AssertionStatementSim, FinalDeferredActionFiresAfterFollowingStmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    assert final (1) y = 8'd55;\n"
      "    y = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §16.4 prose: when the assertion expression evaluates false, the fail
// branch runs (not the pass branch). The deferral routing applies the
// same way as the pass branch — verify the fail action lands in the
// later region by chaining it with a follow-on inline assignment.
TEST(AssertionStatementSim, ObservedDeferredFailActionDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] z;\n"
      "  initial begin\n"
      "    z = 8'd0;\n"
      "    assert #0 (0) else z = 8'd77;\n"
      "    z = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("z");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §16.4 P16: "In addition to deferred assert statements, deferred assume
// and cover statements are also defined. Other than the deferred
// evaluation as described in this subclause, these assume and cover
// statements behave the same way as the simple immediate assume and cover
// statements." The cover form must also route its pass action through
// the §16.4 P13 deferral path.
TEST(AssertionStatementSim, DeferredCoverActionDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] w;\n"
      "  initial begin\n"
      "    w = 8'd0;\n"
      "    cover #0 (1) w = 8'd33;\n"
      "    w = 8'd66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §16.4 P7 (first half): "the deferred assertion's expression is
// evaluated at the time the deferred assertion statement is processed."
// The expression must be sampled at the processing instant — NOT at the
// time the action eventually runs. We assert `q == 0` at processing
// time (so the pass branch is taken), then mutate q before the action
// fires. If the expression had been evaluated at action time it would
// see q == 1 and the fail branch would run instead. Observing q == 44
// proves the expression's processing-instant value (q == 0 → true)
// drove the routing.
TEST(AssertionStatementSim, ObservedExpressionEvaluatedAtProcessingTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    q = 8'd0;\n"
      "    assert #0 (q == 0) q = 8'd44; else q = 8'd77;\n"
      "    q = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// §16.4 P11: "Actual argument expressions that are passed by value,
// including function calls, shall be fully evaluated at the instant the
// deferred assertion expression is evaluated." The actual `s` is sampled
// at the schedule point (= 5), then `s` is mutated to 99 before the
// deferred action fires. The user task writes its formal back into
// `result`; observing `result == 5` proves the action saw the schedule-
// time value of the actual, not the action-time value.
TEST(AssertionStatementSim, DeferredCallArgEvaluatedAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] s;\n"
      "  logic [7:0] result;\n"
      "  task capture(input logic [7:0] v); result = v; endtask\n"
      "  initial begin\n"
      "    s = 8'd5;\n"
      "    result = 8'd0;\n"
      "    assert #0 (1) capture(s);\n"
      "    s = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §16.4 P13 × P16: the Reactive-region routing applies to deferred
// `assume` too. The deferred assume's pass action must land in the
// Reactive region (after the inline post-assert assignment), so the
// observed final value reflects the deferred write.
TEST(AssertionStatementSim, ObservedDeferredAssumeActionDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    assume #0 (1) a = 8'd88;\n"
      "    a = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

}  // namespace
