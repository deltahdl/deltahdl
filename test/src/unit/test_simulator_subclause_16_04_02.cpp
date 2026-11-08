#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_queues.h"

using namespace delta;

namespace {

struct FlushPointFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

TEST(DeferredFlushPoints, EventResumeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, WaitResumeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kWaitResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, AlwaysCombSignalDeltaClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("alc", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alc",
                                FlushPointReason::kAlwaysCombSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alc").Size(), 0u);
}

TEST(DeferredFlushPoints, AlwaysLatchSignalDeltaClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("alt", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alt",
                                FlushPointReason::kAlwaysLatchSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alt").Size(), 0u);
}

TEST(DeferredFlushPoints, DisableOuterScopeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, NoneReasonDoesNotClearQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kNone);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredFlushPoints, FlushOnEmptyQueueIsSafeNoOp) {
  FlushPointFixture f;
  f.engine.OnDeferredFlushPoint("nonexistent",
                                FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("nonexistent").Size(), 0u);
}

TEST(DeferredFlushPointsLive, AlwaysCombRetriggerFlushesDeferredReport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  int flag = 0;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "    assert #0 (!(a && b)) else set_flag();\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(DeferredFlushPointsLive, AlwaysLatchRetriggerFlushesDeferredReport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic en, d;\n"
      "  logic [7:0] q;\n"
      "  int flag = 0;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  always_latch begin\n"
      "    if (en) q = d;\n"
      "    assert #0 (!en) else set_flag();\n"
      "  end\n"
      "  initial begin\n"
      "    d = 1'b1;\n"
      "    en = 1'b1;\n"
      "    en <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(DeferredFlushPointsLive, SettledAlwaysCombDeferredReportExecutes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a;\n"
      "  logic [7:0] z;\n"
      "  int flag = 0;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else z = 8'd0;\n"
      "    assert #0 (a) else set_flag();\n"
      "  end\n"
      "  initial a = 1'b0;\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeferredFlushPointsLive, EventControlResumeFlushesDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  initial begin\n"
      "    assert #0 (0) else set_flag();\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
}

TEST(DeferredFlushPointsLive, MaturedDeferredReportSurvivesLaterEventResume) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  initial begin\n"
      "    assert #0 (0) else set_flag();\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

TEST(DeferredFlushPointsLive, WaitResumeFlushesDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  logic ready;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  initial begin\n"
      "    ready = 1'b0;\n"
      "    assert #0 (0) else set_flag();\n"
      "    wait (ready);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    ready = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
}

TEST(DeferredFlushPointsLive, WaitOrderResumeFlushesDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  event a;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  initial begin\n"
      "    assert #0 (0) else set_flag();\n"
      "    wait_order (a);\n"
      "    x = 8'd5;\n"
      "  end\n"
      "  initial #0 -> a;\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
}

TEST(DeferredFlushPointsLive, AlwaysCombRetriggerFlushesDefaultErrorReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "    assert #0 (!(a && b));\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DeferredFlushPointsLive, AlwaysCombRetriggerFlushesFinalDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "    assert final (!(a && b)) else $error(\"final fail\");\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DeferredFlushPointsLive, WaitAlreadyTrueDoesNotFlushDeferredReport) {
  SimFixture f;
  auto* flag = RunAndFindVar(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  function void set_flag; flag = 1; endfunction\n"
      "  initial begin\n"
      "    assert #0 (0) else set_flag();\n"
      "    wait (1'b1);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
}

TEST(DeferredFlushPointsLive, PerProcessFlushDoesNotClearOtherProcessReport) {
  SimFixture f;
  auto* flag_a = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int flag_a = 0;\n"
      "  int flag_b = 0;\n"
      "  function void set_flag_a; flag_a = 1; endfunction\n"
      "  function void set_flag_b; flag_b = 1; endfunction\n"
      "  initial begin\n"
      "    assert #0 (0) else set_flag_a();\n"
      "    @e;\n"
      "  end\n"
      "  initial begin\n"
      "    assert #0 (0) else set_flag_b();\n"
      "  end\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n",
      f, "flag_a");
  ASSERT_NE(flag_a, nullptr);
  EXPECT_EQ(flag_a->value.ToUint64(), 0u);
  auto* flag_b = f.ctx.FindVariable("flag_b");
  ASSERT_NE(flag_b, nullptr);
  EXPECT_EQ(flag_b->value.ToUint64(), 1u);
}

TEST(DeferredFlushPointsLive, CastTaskInActionBlockRaisesRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    c = GREEN;\n"
      "    assert #0 (0) else $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$cast task could not assign",
                            6, "6.24.2"));
}

TEST(DeferredFlushPointsLive, FlushedDeferredCoverIsNotCountedAsCovered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  always_comb begin : b1\n"
      "    c1: cover (b != a);\n"
      "    c2: cover #0 (b != a);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 5;\n"
      "    #0 b = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const auto& results = f.ctx.ImmediateCovers().Results();
  ASSERT_EQ(results.size(), 2u);
  EXPECT_EQ(results[0].scope, "t.b1.c1");
  EXPECT_EQ(results[0].evaluated, 3u);
  EXPECT_EQ(results[0].succeeded, 1u);
  EXPECT_EQ(results[1].scope, "t.b1.c2");
  EXPECT_EQ(results[1].evaluated, 2u);
  EXPECT_EQ(results[1].succeeded, 0u);
}

TEST(DeferredFlushPointsLive, ActionBlockArgumentsAreEvaluatedOnEveryFailure) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit my_cond = 1;\n"
      "  int opcode;\n"
      "  int seen;\n"
      "  function int error_type(input int opcode);\n"
      "    func_assert: assert (opcode < 64) else $display(\"Opcode "
      "error.\");\n"
      "    if (opcode < 32) return 0; else return 1;\n"
      "  endfunction\n"
      "  always_comb begin : b1\n"
      "    seen = opcode;\n"
      "    if (!my_cond) $display(\"b1: failing pass with opcode %0d\", "
      "opcode);\n"
      "    a1: assert #0 (my_cond) else\n"
      "      $info(\"Error on operation of type %0d\", error_type(opcode));\n"
      "    a2: assert #0 (my_cond) else void'(error_type(opcode));\n"
      "  end\n"
      "  initial begin\n"
      "    #1 opcode = 64; my_cond = 0;\n"
      "    $display(\"initial: after the writes of 64 and 0\");\n"
      "    #0 opcode = 0;\n"
      "    $display(\"initial: after the write of 0\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "b1: failing pass with opcode 64\n"
            "Opcode error.\n"
            "initial: after the writes of 64 and 0\n"
            "b1: failing pass with opcode 0\n"
            "initial: after the write of 0\n"
            "[1] INFO t.b1.a1 (<test>:13): Error on operation of type 0\n");
}

TEST(DeferredFlushPointsLive,
     ActionBlockArgumentsAreEvaluatedOnEveryFailureWithAFormalNamedApart) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit my_cond = 1;\n"
      "  int opcode;\n"
      "  int seen;\n"
      "  function int error_type(input int op);\n"
      "    func_assert: assert (op < 64) else $display(\"Opcode error.\");\n"
      "    if (op < 32) return 0; else return 1;\n"
      "  endfunction\n"
      "  always_comb begin : b1\n"
      "    seen = opcode;\n"
      "    if (!my_cond) $display(\"b1: failing pass with opcode %0d\", "
      "opcode);\n"
      "    a1: assert #0 (my_cond) else\n"
      "      $info(\"Error on operation of type %0d\", error_type(opcode));\n"
      "    a2: assert #0 (my_cond) else void'(error_type(opcode));\n"
      "  end\n"
      "  initial begin\n"
      "    #1 opcode = 64; my_cond = 0;\n"
      "    $display(\"initial: after the writes of 64 and 0\");\n"
      "    #0 opcode = 0;\n"
      "    $display(\"initial: after the write of 0\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "b1: failing pass with opcode 64\n"
            "Opcode error.\n"
            "initial: after the writes of 64 and 0\n"
            "b1: failing pass with opcode 0\n"
            "initial: after the write of 0\n"
            "[1] INFO t.b1.a1 (<test>:13): Error on operation of type 0\n");
}

}  // namespace
