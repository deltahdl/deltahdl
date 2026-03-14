#include <gtest/gtest.h>

#include <string>

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

// =============================================================================
// §16.4 SVA Engine: DeferredAssertion action dispatch
// =============================================================================

TEST(DeferredAssertSim, PassActionInvoked) {
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

TEST(DeferredAssertSim, FailActionInvoked) {
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

TEST(DeferredAssertSim, NoActionBlockDoesNotCrash) {
  DeferredAssertion da;
  da.condition_val = 0;

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(true);
}

TEST(DeferredAssertSim, PassWithBothActions) {
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

TEST(DeferredAssertSim, FailWithBothActions) {
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

TEST(DeferredAssertSim, PassActionCounter) {
  DeferredAssertion da;
  da.condition_val = 1;
  int pass_count = 0;
  da.pass_action = [&pass_count]() { ++pass_count; };
  ExecuteDeferredAssertionAction(da);
  EXPECT_EQ(pass_count, 1);
}

TEST(DeferredAssertSim, FailActionCounter) {
  DeferredAssertion da;
  da.condition_val = 0;
  int fail_count = 0;
  da.fail_action = [&fail_count]() { ++fail_count; };
  ExecuteDeferredAssertionAction(da);
  EXPECT_EQ(fail_count, 1);
}

// =============================================================================
// §16.4 SVA Engine: queue/flush lifecycle
// =============================================================================

TEST(DeferredAssertSim, EngineDefaultState) {
  SvaEngine engine;
  EXPECT_EQ(engine.DeferredQueueSize(), 0u);
}

TEST(DeferredAssertSim, QueueAndFlushSingleAssertion) {
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

TEST(DeferredAssertSim, FlushClearsQueue) {
  SvaFixture f;

  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueueDeferredAssertion(da);
  EXPECT_EQ(f.engine.DeferredQueueSize(), 1u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);
}

TEST(DeferredAssertSim, MultipleAssertionsQueued) {
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

TEST(DeferredAssertSim, MixedPassAndFailQueuedAndFlushed) {
  SvaFixture f;
  int pass_count = 0;
  int fail_count = 0;

  for (int i = 0; i < 4; ++i) {
    DeferredAssertion da;
    da.condition_val = (i % 2 == 0) ? 1 : 0;
    da.instance_name = "mixed_" + std::to_string(i);
    da.pass_action = [&pass_count]() { ++pass_count; };
    da.fail_action = [&fail_count]() { ++fail_count; };
    f.engine.QueueDeferredAssertion(da);
  }

  EXPECT_EQ(f.engine.DeferredQueueSize(), 4u);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);
  f.scheduler.Run();

  EXPECT_EQ(pass_count, 2);
  EXPECT_EQ(fail_count, 2);
}

// =============================================================================
// §16.4.1 Deferred assertion reporting
// =============================================================================

TEST(DeferredAssertSim, FailScheduledInReactiveRegion) {
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

TEST(DeferredAssertSim, ActionDeferredNotImmediate) {
  SvaFixture f;
  bool observed_executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "deferred_observed";
  da.pass_action = [&observed_executed]() { observed_executed = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});

  // After flush but before scheduler run, action should not have executed yet.
  EXPECT_FALSE(observed_executed);

  f.scheduler.Run();
  EXPECT_TRUE(observed_executed);
}

TEST(DeferredAssertSim, FinalAssertionQueuedWithFlag) {
  // §16.4.1: Final deferred assertions use is_final flag.
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.is_final = true;
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(executed);
}

TEST(DeferredAssertSim, FinalAssertionFailExecuted) {
  // §16.4.1: Final deferred assertion failure.
  SvaFixture f;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 0;
  da.is_final = true;
  da.fail_action = [&fail_called]() { fail_called = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(fail_called);
}

// =============================================================================
// §16.4.2 Deferred assertion flush points
// =============================================================================

TEST(DeferredAssertSim, FlushPointClearsProcessQueue) {
  // §16.4.2: Reaching a flush point clears pending reports.
  SvaFixture f;
  int count = 0;

  for (int i = 0; i < 3; ++i) {
    DeferredAssertion da;
    da.condition_val = 0;
    da.process_id = 1;
    da.fail_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }

  EXPECT_EQ(f.engine.DeferredQueueSize(), 3u);

  // Flush point: clears all pending reports for process 1.
  f.engine.ClearQueueForProcess(1);
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);

  // No reports should execute.
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);
}

TEST(DeferredAssertSim, FlushPointOnlyAffectsOwnProcess) {
  // §16.4.2: Flush point only clears the affected process.
  SvaFixture f;
  int count_p1 = 0;
  int count_p2 = 0;

  DeferredAssertion da1;
  da1.condition_val = 1;
  da1.process_id = 1;
  da1.pass_action = [&count_p1]() { ++count_p1; };
  f.engine.QueueDeferredAssertion(da1);

  DeferredAssertion da2;
  da2.condition_val = 1;
  da2.process_id = 2;
  da2.pass_action = [&count_p2]() { ++count_p2; };
  f.engine.QueueDeferredAssertion(da2);

  // Flush only process 1.
  f.engine.ClearQueueForProcess(1);
  EXPECT_EQ(f.engine.DeferredQueueSize(), 1u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count_p1, 0);
  EXPECT_EQ(count_p2, 1);
}

TEST(DeferredAssertSim, QueueSizeForProcess) {
  SvaFixture f;

  DeferredAssertion da1;
  da1.process_id = 1;
  f.engine.QueueDeferredAssertion(da1);
  f.engine.QueueDeferredAssertion(da1);

  DeferredAssertion da2;
  da2.process_id = 2;
  f.engine.QueueDeferredAssertion(da2);

  EXPECT_EQ(f.engine.DeferredQueueSizeForProcess(1), 2u);
  EXPECT_EQ(f.engine.DeferredQueueSizeForProcess(2), 1u);
  EXPECT_EQ(f.engine.DeferredQueueSizeForProcess(3), 0u);
}

// =============================================================================
// §16.4.3 Deferred assertions outside procedural code (module-level)
// =============================================================================

TEST(DeferredAssertSim, StaticAssertHash0ModuleLevel) {
  // §16.4.3: Static deferred assertion at module level (treated as always_comb).
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x = 8'd42;\n"
      "  assert #0 (x != 0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertSim, StaticAssertFinalModuleLevel) {
  // §16.4.3: Final deferred assertion at module level.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x = 8'd42;\n"
      "  assert final (x != 0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// §16.4.4 Disabling deferred assertions
// =============================================================================

TEST(DeferredAssertSim, DisableAssertionCancelsPendingReports) {
  // §16.4.4: Specific deferred assertion may be disabled; pending reports cancelled.
  SvaFixture f;
  int count = 0;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "cancel_target";
  da.pass_action = [&count]() { ++count; };
  f.engine.QueueDeferredAssertion(da);
  f.engine.QueueDeferredAssertion(da);

  EXPECT_EQ(f.engine.DeferredQueueSize(), 2u);
  f.engine.CancelReportsForAssertion("cancel_target");
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);
}

TEST(DeferredAssertSim, DisableAssertionOnlyCancelsMatchingInstance) {
  // §16.4.4: Cancel only affects the named instance.
  SvaFixture f;
  int count_a = 0;
  int count_b = 0;

  DeferredAssertion da_a;
  da_a.condition_val = 1;
  da_a.instance_name = "a";
  da_a.pass_action = [&count_a]() { ++count_a; };
  f.engine.QueueDeferredAssertion(da_a);

  DeferredAssertion da_b;
  da_b.condition_val = 1;
  da_b.instance_name = "b";
  da_b.pass_action = [&count_b]() { ++count_b; };
  f.engine.QueueDeferredAssertion(da_b);

  f.engine.CancelReportsForAssertion("a");
  EXPECT_EQ(f.engine.DeferredQueueSize(), 1u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count_a, 0);
  EXPECT_EQ(count_b, 1);
}

TEST(DeferredAssertSim, DisableOutermostScopeFlushesQueue) {
  // §16.4.4: disable applied to outermost scope flushes deferred queue.
  SvaFixture f;
  int count = 0;

  for (int i = 0; i < 3; ++i) {
    DeferredAssertion da;
    da.condition_val = 0;
    da.process_id = 1;
    da.fail_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }

  // Simulates disable of outermost scope: clear entire process queue.
  f.engine.ClearQueueForProcess(1);
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);
}

TEST(DeferredAssertSim, AssertoffDisablesAssertion) {
  // Moved from test_simulator_clause_16.cpp (was SimCh16::AssertionControlAssertoffDisablesAssertion)
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "disabled_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.GetControl().SetOff("disabled_assert");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(executed);
  EXPECT_FALSE(f.engine.GetControl().IsEnabled("disabled_assert"));
}

TEST(DeferredAssertSim, AssertonReenablesAssertion) {
  // Moved from test_simulator_clause_16.cpp (was SimCh16::AssertionControlAssertonReenablesAssertion)
  SvaFixture f;
  bool executed = false;

  f.engine.GetControl().SetOff("reenable_assert");
  EXPECT_FALSE(f.engine.GetControl().IsEnabled("reenable_assert"));

  f.engine.GetControl().SetOn("reenable_assert");
  EXPECT_TRUE(f.engine.GetControl().IsEnabled("reenable_assert"));

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "reenable_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(executed);
}

TEST(DeferredAssertSim, AssertkillRemovesPendingReports) {
  // Moved from test_simulator_clause_16.cpp (was SimCh16::AssertionControlAssertkillRemovesPendingAssertions)
  SvaFixture f;
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.instance_name = "kill_target";
    da.pass_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }

  EXPECT_EQ(f.engine.DeferredQueueSize(), 5u);
  f.engine.KillAssertionsForInstance("kill_target");
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);

  EXPECT_TRUE(f.engine.GetControl().WasKilled("kill_target"));
}

// =============================================================================
// §16.4.5 Deferred assertions and multiple processes
// =============================================================================

TEST(DeferredAssertSim, IndependentQueuesPerProcess) {
  // §16.4.5: Each process has its own independent deferred assertion queue.
  SvaFixture f;
  int count_p1 = 0;
  int count_p2 = 0;

  for (int i = 0; i < 3; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.process_id = 1;
    da.pass_action = [&count_p1]() { ++count_p1; };
    f.engine.QueueDeferredAssertion(da);
  }

  for (int i = 0; i < 2; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.process_id = 2;
    da.pass_action = [&count_p2]() { ++count_p2; };
    f.engine.QueueDeferredAssertion(da);
  }

  EXPECT_EQ(f.engine.DeferredQueueSizeForProcess(1), 3u);
  EXPECT_EQ(f.engine.DeferredQueueSizeForProcess(2), 2u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count_p1, 3);
  EXPECT_EQ(count_p2, 2);
}

TEST(DeferredAssertSim, FlushOneProcessDoesNotAffectAnother) {
  // §16.4.5: Clearing one process queue leaves others intact.
  SvaFixture f;
  int count_p1 = 0;
  int count_p2 = 0;

  DeferredAssertion da1;
  da1.condition_val = 1;
  da1.process_id = 1;
  da1.pass_action = [&count_p1]() { ++count_p1; };
  f.engine.QueueDeferredAssertion(da1);

  DeferredAssertion da2;
  da2.condition_val = 1;
  da2.process_id = 2;
  da2.pass_action = [&count_p2]() { ++count_p2; };
  f.engine.QueueDeferredAssertion(da2);

  f.engine.ClearQueueForProcess(1);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count_p1, 0);
  EXPECT_EQ(count_p2, 1);
}

// =============================================================================
// §16.4 Integration: full pipeline with elaboration and lowering
// =============================================================================

TEST(DeferredAssertSim, AssertHash0PassActionExecuted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (1) x = 8'd44;\n"
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

TEST(DeferredAssertSim, AssertHash0FailActionExecuted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (0) x = 8'd44; else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(DeferredAssertSim, AssertFinalPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert final (1) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(DeferredAssertSim, AssertFinalFailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert final (0) x = 8'd55; else x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(DeferredAssertSim, AssumeHash0PassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume #0 (1) x = 8'd60;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 60u);
}

TEST(DeferredAssertSim, AssumeHash0FailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume #0 (0) x = 8'd60; else x = 8'd70;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 70u);
}

TEST(DeferredAssertSim, AssumeFinalPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume final (1) x = 8'd65;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 65u);
}

TEST(DeferredAssertSim, AssumeFinalFailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume final (0) x = 8'd65; else x = 8'd75;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 75u);
}

TEST(DeferredAssertSim, CoverHash0PassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    cover #0 (1) x = 8'd80;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 80u);
}

TEST(DeferredAssertSim, CoverHash0FalseSkipsAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    cover #0 (0) x = 8'd80;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(DeferredAssertSim, CoverFinalPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    cover final (1) x = 8'd85;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 85u);
}

TEST(DeferredAssertSim, CoverFinalFalseSkipsAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    cover final (0) x = 8'd85;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(DeferredAssertSim, AssertHash0FalseNoElseDefaultError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    assert #0 (0);\n"
      "    x = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(DeferredAssertSim, AssertFinalFalseNoElseDefaultError) {
  // §16.4.1: final deferred assert with no else still calls default $error.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    assert final (0);\n"
      "    x = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(DeferredAssertSim, CoverHash0FalseNoDefaultError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    cover #0 (0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

TEST(DeferredAssertSim, CoverFinalFalseNoDefaultError) {
  // §16.4: cover does NOT emit default $error on false, even for final.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    cover final (0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

TEST(DeferredAssertSim, AssumeHash0FalseNoElseDefaultError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume #0 (0);\n"
      "    x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(DeferredAssertSim, AssumeFinalFalseNoElseDefaultError) {
  // §16.4.1: final deferred assume with no else still calls default $error.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume final (0);\n"
      "    x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

}  // namespace
