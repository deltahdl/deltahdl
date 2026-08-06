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

// Every deferred action below is a single subroutine call, because §16.4 says
// "the pass and fail statements in a deferred assertion's action_block, if
// present, shall each consist of a single subroutine call" -- an assignment is
// not one. An observed (#0) action calls a void function that writes the
// variable under test, which is legal because §16.4 schedules that call in the
// Reactive region. A final action cannot use that vehicle: §16.4 requires its
// subroutine to "be one that may be legally called in the Postponed region",
// and §4.4.2.9 says of that region that "it is illegal to write values to any
// net or variable", so the final test reports through a severity system task
// instead and observes it with LastSeverity().

TEST(AssertionStatementSim, ObservedDeferredActionFiresAfterFollowingStmt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x_44; x = 8'd44; endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (1) set_x_44();\n"
      "    x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// The final form of the test above. Its claim is unchanged -- the pass action
// runs after the statement that follows the assertion -- but it is read off the
// severity rather than a variable, and the subroutine is a user task rather
// than a system task, which §16.4 lists first among the permitted forms. The
// task's body only reports, so it is one that "may be legally called in the
// Postponed region". The inline $error runs in the Active region where the
// process reaches it and the deferred report runs later in the Postponed
// region, so the last message is the deferred one; run inline, "inline" would
// be last.
TEST(AssertionStatementSim, FinalDeferredActionFiresAfterFollowingStmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task announce; $warning(\"postponed\"); endtask\n"
      "  initial begin\n"
      "    assert final (1) announce();\n"
      "    $error(\"inline\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "postponed");
}

TEST(AssertionStatementSim, ObservedDeferredFailActionDeferred) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] z;\n"
      "  function void set_z_77; z = 8'd77; endfunction\n"
      "  initial begin\n"
      "    z = 8'd0;\n"
      "    assert #0 (0) else set_z_77();\n"
      "    z = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f, "z");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(AssertionStatementSim, DeferredCoverActionDeferred) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] w;\n"
      "  function void set_w_33; w = 8'd33; endfunction\n"
      "  initial begin\n"
      "    w = 8'd0;\n"
      "    cover #0 (1) set_w_33();\n"
      "    w = 8'd66;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(AssertionStatementSim, ObservedExpressionEvaluatedAtProcessingTime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  function void set_q_44; q = 8'd44; endfunction\n"
      "  function void set_q_77; q = 8'd77; endfunction\n"
      "  initial begin\n"
      "    q = 8'd0;\n"
      "    assert #0 (q == 0) set_q_44(); else set_q_77();\n"
      "    q = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(AssertionStatementSim, DeferredCallArgEvaluatedAtScheduleTime) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §16.4: an actual argument passed to a deferred assertion action subroutine is
// fully evaluated -- including any function call in the argument expression --
// at the instant the deferred assertion's expression is evaluated, not when the
// deferred call later runs. The argument is dbl(s); although s is overwritten
// after the assertion is processed, the captured value reflects dbl of the
// value s held at processing time.
TEST(AssertionStatementSim, DeferredFunctionCallArgEvaluatedAtScheduleTime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] s;\n"
      "  logic [7:0] result;\n"
      "  function logic [7:0] dbl(input logic [7:0] v);\n"
      "    dbl = v << 1;\n"
      "  endfunction\n"
      "  task capture(input logic [7:0] v); result = v; endtask\n"
      "  initial begin\n"
      "    s = 8'd5;\n"
      "    result = 8'd0;\n"
      "    assert #0 (1) capture(dbl(s));\n"
      "    s = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);  // dbl(5), captured at processing time
}

TEST(AssertionStatementSim, ObservedDeferredAssumeActionDeferred) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  function void set_a_88; a = 8'd88; endfunction\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    assume #0 (1) set_a_88();\n"
      "    a = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

}  // namespace
