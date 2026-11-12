#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_queues.h"
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
  EXPECT_EQ(var->value.ToUint64(), 10u);
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

TEST(AssertionStatementSim, EachDeferredReportCarriesItsOwnByValueActual) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  int result;\n"
      "  task fold(input int n); result = result * 10 + n; endtask\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    for (i = 0; i < 3; i++) assert #0 (1) fold(i);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(DeferredAssertionSim, AClassMethodsDeferredActionRunsOnItsObject) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  int f = 0, p = 0, n = 0;\n"
      "  function void ff(); f++; endfunction\n"
      "  function void pp(); p++; endfunction\n"
      "  function void nn(); this.n++; endfunction\n"
      "  function void chk(int x);\n"
      "    a: assert #0 (x > 0) pp(); else ff();\n"
      "    b: assert #0 (x > 0) else this.nn();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int fs = 0;\n"
      "  function void ffs(); fs++; endfunction\n"
      "  function void chk_static(int x);\n"
      "    a: assert #0 (x > 0) else ffs();\n"
      "  endfunction\n"
      "  C c = new;\n"
      "  initial begin\n"
      "    #10 c.chk(-1);\n"
      "    #10 c.chk(2);\n"
      "    #10 chk_static(-3);\n"
      "    #5 $display(\"f=%0d p=%0d n=%0d fs=%0d\", c.f, c.p, c.n, fs);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "f=1 p=1 n=1 fs=1\n");
}

TEST(DeferredAssertionSim, AClassMethodsDeferredActionFromAnAlwaysProcedure) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  int f = 0, p = 0;\n"
      "  function void ff(); f++; endfunction\n"
      "  function void pp(); p++; endfunction\n"
      "  function void chk(int x);\n"
      "    a: assert #0 (x > 0) pp(); else ff();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic trig = 0;\n"
      "  int val = 0;\n"
      "  C c = new;\n"
      "  always @(trig) c.chk(val);\n"
      "  initial begin\n"
      "    #10 val = -1; trig = 1;\n"
      "    #10 val = 2; trig = 0;\n"
      "    #5 $display(\"f=%0d p=%0d\", c.f, c.p);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "f=1 p=1\n");
}

TEST(DeferredAssertionSim, APassStatementThatIsNoCallIsReportedAndNotRun) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x = 0, done = 0;\n"
      "  initial begin\n"
      "    a: assert #0 (1) x = 5;\n"
      "    done = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "deferred assertion pass action shall be a single subroutine call", 4,
      "16.4"));
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
}

}  // namespace
