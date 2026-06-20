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
