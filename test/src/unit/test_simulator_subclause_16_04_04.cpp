#include <gtest/gtest.h>

#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_queues.h"

using namespace delta;

namespace {

struct DeferredDisableFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;

  void QueueObserved(std::string_view process_id, std::string_view instance) {
    DeferredAssertion da;
    da.condition_val = 0;
    da.instance_name = std::string(instance);
    engine.QueuePendingReport(process_id, da, DeferralKind::kObserved);
  }
};

TEST(DeferredDisableSpecific, CancelsOnlyNamedAssertionPendingReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(
      f.engine.GetDeferredReportQueue("p0").Entries().front().da.instance_name,
      "a2");
}

TEST(DeferredDisableSpecific, LeavesMaturedReportOfNamedAssertion) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.engine.MatureObservedReports("p0");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredDisableOutermost, FlushesAllPendingReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredDisableOutermost, LeavesMaturedReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.engine.MatureObservedReports("p0");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);
}

TEST(DeferredDisableNoFlush, TaskLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions("p0", DisableTarget::kTask, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

TEST(DeferredDisableNoFlush, NonOutermostScopeLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kNonOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

TEST(DeferredDisableSpecific, UnknownAssertionNameLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "missing");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

TEST(DeferredDisableSpecific, CancelsAllPendingReportsOfSameAssertion) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 3u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(
      f.engine.GetDeferredReportQueue("p0").Entries().front().da.instance_name,
      "a2");
}

TEST(DeferredDisableSpecific, DoesNotAffectOtherProcessQueue) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p1", "a1");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p1").Size(), 1u);
}

TEST(DeferredDisableOutermost, EmptyQueueIsSafeNoOp) {
  DeferredDisableFixture f;

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredDisableOutermost, AllMaturedQueueSurvives) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  f.engine.MatureObservedReports("p0");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

TEST(DeferredDisableOutermost, DoesNotAffectOtherProcessQueue) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p1", "a1");

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p1").Size(), 1u);
}

TEST(DisableOutermostScopeLive,
     CrossProcessDisableFlushesQueuedDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  int flag = 0;\n"
      "  function void set_flag();\n"
      "    flag = 1;\n"
      "  endfunction\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0) else set_flag();\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
}

TEST(DisableOutermostScopeLive, DisableFlushesEveryPendingReportOfProcess) {
  SimFixture f;
  auto* flag1 = RunAndFindVar(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  int flag1 = 0;\n"
      "  int flag2 = 0;\n"
      "  function void set_flag1();\n"
      "    flag1 = 1;\n"
      "  endfunction\n"
      "  function void set_flag2();\n"
      "    flag2 = 1;\n"
      "  endfunction\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0) else set_flag1();\n"
      "    assert #0 (0) else set_flag2();\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "flag1");
  ASSERT_NE(flag1, nullptr);
  EXPECT_EQ(flag1->value.ToUint64(), 0u);
  auto* flag2 = f.ctx.FindVariable("flag2");
  ASSERT_NE(flag2, nullptr);
  EXPECT_EQ(flag2->value.ToUint64(), 0u);
}

TEST(DisableOutermostScopeLive, WithoutDisableDeferredReportExecutes) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  logic a = 0;\n"
      "  int flag = 0;\n"
      "  function void set_flag();\n"
      "    flag = 1;\n"
      "  endfunction\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0) else set_flag();\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

TEST(DisableNonOutermostScopeLive,
     InnerBlockDisableDoesNotFlushDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  function void set_flag();\n"
      "    flag = 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    begin : inner\n"
      "      assert #0 (0) else set_flag();\n"
      "      disable inner;\n"
      "    end\n"
      "    x = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 7u);
}

TEST(DisableNonOutermostScopeLive, TaskDisableDoesNotFlushDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  function void set_flag();\n"
      "    flag = 1;\n"
      "  endfunction\n"
      "  task do_check;\n"
      "    begin\n"
      "      assert #0 (0) else set_flag();\n"
      "      disable do_check;\n"
      "    end\n"
      "  endtask\n"
      "  initial begin\n"
      "    do_check;\n"
      "    x = 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
}

TEST(DisableOutermostScopeLive, DisableFlushesFinalDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert final (0) else $error(\"b2 final report\");\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DisableOutermostScopeLive, FlushedProcedureStaysArmedForItsNextTrigger) {
  SimFixture f;
  auto* runs = RunAndFindVar(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  int flag = 0;\n"
      "  int runs = 0;\n"
      "  function void set_flag();\n"
      "    flag = 1;\n"
      "  endfunction\n"
      "  always @(a) begin : b2\n"
      "    runs = runs + 1;\n"
      "    assert #0 (runs > 1) else set_flag();\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "    #1 a = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "runs");
  ASSERT_NE(runs, nullptr);
  EXPECT_EQ(runs->value.ToUint64(), 2u);
}

TEST(DisableOutermostScopeLive, DisableFlushesDefaultErrorReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0);\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DisableNonOutermostScopeLive, InnerBlockDisableDoesNotFlushFinalReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x = 0;\n"
      "  initial begin\n"
      "    begin : inner\n"
      "      assert final (0) else $error(\"inner final report\");\n"
      "      disable inner;\n"
      "    end\n"
      "    x = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 7u);
}

TEST(DisableSpecificAssertionLive, CancelsItsPendingReportAndProcessContinues) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  function void set_flag();\n"
      "    flag = 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a1: assert #0 (0) else set_flag();\n"
      "    disable a1;\n"
      "    x = 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

TEST(DisableSpecificAssertionLive, LeavesOtherAssertionsPendingReports) {
  SimFixture f;
  auto* flag1 = RunAndFindVar(
      "module t;\n"
      "  int flag1 = 0;\n"
      "  int flag2 = 0;\n"
      "  function void set_flag1();\n"
      "    flag1 = 1;\n"
      "  endfunction\n"
      "  function void set_flag2();\n"
      "    flag2 = 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a1: assert #0 (0) else set_flag1();\n"
      "    a2: assert #0 (0) else set_flag2();\n"
      "    disable a1;\n"
      "  end\n"
      "endmodule\n",
      f, "flag1");
  ASSERT_NE(flag1, nullptr);
  EXPECT_EQ(flag1->value.ToUint64(), 0u);
  auto* flag2 = f.ctx.FindVariable("flag2");
  ASSERT_NE(flag2, nullptr);
  EXPECT_EQ(flag2->value.ToUint64(), 1u);
}

}  // namespace
