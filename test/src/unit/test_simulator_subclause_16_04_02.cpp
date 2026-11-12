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

const char kSay[] =
    "  function void say(input string s); $display(\"%0t %s\", $time, s); "
    "endfunction\n";

std::string AroundTheInitial(const std::string& items,
                             const std::string& body) {
  return std::string(
             "module t;\n"
             "  logic clk = 0, c = 1, d = 1, y, rdy = 0;\n"
             "  event e, f;\n") +
         kSay + items + "  initial begin : p\n" + body +
         "  end\n"
         "endmodule\n";
}

std::string Captured(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

struct Resume {
  const char* items;
  const char* body;
};

void ExpectFlushed(const Resume& r) {
  EXPECT_EQ(Captured(AroundTheInitial(r.items, r.body)), "0 resumed\n")
      << r.body;
}

TEST(DeferredFlushPointsLive, EveryEventControlFormResumesAtAFlushPoint) {
  const Resume kCases[] = {
      {"  initial #0 clk = 1;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    @(posedge clk);\n    say(\"resumed\");\n"},
      {"  initial #0 -> e;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    @(e iff c);\n    say(\"resumed\");\n"},
      {"  initial #0 -> f;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    @(e or f);\n    say(\"resumed\");\n"},
      {"  clocking cb @(posedge clk); endclocking\n"
       "  initial #0 clk = 1;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    @(cb);\n    say(\"resumed\");\n"},
      {"  task automatic wait_e; @(e); endtask\n"
       "  initial #0 -> e;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    wait_e();\n    say(\"resumed\");\n"},
  };
  for (const auto& r : kCases) ExpectFlushed(r);
}

TEST(DeferredFlushPointsLive, ASequenceEventResumeFlushesAFinalReport) {
  ExpectFlushed(
      {"  sequence s; @(posedge clk) 1; endsequence\n"
       "  initial #0 clk = 1;\n",
       "    assert final (0) else say(\"flushed\");\n"
       "    @(s);\n    say(\"resumed\");\n"});
}

TEST(DeferredFlushPointsLive, AWaitResumeFlushesAFinalReport) {
  ExpectFlushed({"  initial #0 rdy = 1;\n",
                 "    assert final (0) else say(\"flushed\");\n"
                 "    wait (rdy);\n    say(\"resumed\");\n"});
}

TEST(DeferredFlushPointsLive, AnInterfaceInitialBlockResumeFlushes) {
  EXPECT_EQ(Captured(std::string("interface ifc;\n  event e;\n") + kSay +
                     "  initial begin\n"
                     "    assert #0 (0) else say(\"flushed\");\n"
                     "    @(e);\n"
                     "    say(\"resumed\");\n"
                     "  end\n"
                     "  initial #0 -> e;\n"
                     "endinterface\n"
                     "module t;\n  ifc i();\nendmodule\n"),
            "0 resumed\n");
}

TEST(DeferredFlushPointsLive, AnAlwaysStarResumeFlushes) {
  const std::string kHead =
      std::string("module t;\n  int x;\n") + kSay +
      "  always @* assert #0 (x != 1) else say(\"flushed\");\n"
      "  initial begin\n"
      "    #1 x = 1;\n";
  EXPECT_EQ(Captured(kHead + "    #0 x = 2;\n  end\nendmodule\n"), "");
  EXPECT_EQ(Captured(kHead + "  end\nendmodule\n"), "1 flushed\n");
}

TEST(DeferredFlushPointsLive,
     DISABLED_ABlockingIntraAssignmentEventControlResumeFlushes) {
  const Resume kCases[] = {
      {"  initial #0 -> e;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    y = @(e) d;\n    say(\"resumed\");\n"},
      {"  initial #0 -> e;\n",
       "    assert final (0) else say(\"flushed\");\n"
       "    y = @(e) d;\n    say(\"resumed\");\n"},
      {"  initial #0 -> e;\n",
       "    assert #0 (0) else say(\"flushed\");\n"
       "    y = repeat (1) @(e) d;\n    say(\"resumed\");\n"},
  };
  for (const auto& r : kCases) ExpectFlushed(r);
}

std::string ProgramResumingAt(const std::string& suspend) {
  return Captured(std::string("program p;\n"
                              "  logic d = 1, y, started = 0;\n"
                              "  event e;\n") +
                  kSay +
                  "  initial begin\n"
                  "    assert #0 (0) else say(\"flushed\");\n"
                  "    started = 1;\n    " +
                  suspend +
                  "\n    say(\"resumed\");\n"
                  "  end\n"
                  "  initial begin wait (started); -> e; end\n"
                  "endprogram\n");
}

TEST(DeferredFlushPointsLive, DISABLED_AProgramsEventControlResumeFlushes) {
  EXPECT_EQ(ProgramResumingAt("@(e);"), "0 resumed\n");
}

TEST(DeferredFlushPointsLive,
     DISABLED_AProgramsIntraAssignmentEventControlResumeFlushes) {
  EXPECT_EQ(ProgramResumingAt("y = @(e) d;"), "0 resumed\n");
}

TEST(DeferredFlushPointsLive,
     DISABLED_AClassTasksIntraAssignmentEventControlResumeFlushes) {
  EXPECT_EQ(Captured(std::string("class C;\n  event e;\n  logic y;\n") + kSay +
                     "  task run;\n"
                     "    assert #0 (0) else say(\"flushed\");\n"
                     "    y = @(e) 1'b1;\n"
                     "    say(\"resumed\");\n"
                     "  endtask\n"
                     "endclass\n"
                     "module t;\n"
                     "  C c = new;\n"
                     "  initial c.run();\n"
                     "  initial #0 -> c.e;\n"
                     "endmodule\n"),
            "0 resumed\n");
}

TEST(DeferredFlushPointsLive, DISABLED_AWaitForkResumeFlushes) {
  for (const char* form : {"assert #0", "assert final"}) {
    EXPECT_EQ(Captured(AroundTheInitial(
                  "", std::string("    fork #0 say(\"child\"); join_none\n"
                                  "    ") +
                          form +
                          " (0) else say(\"flushed\");\n"
                          "    wait fork;\n    say(\"resumed\");\n")),
              "0 child\n0 resumed\n")
        << form;
  }
}

TEST(DeferredFlushPointsLive, AShortCircuitedFunctionsReportIsFlushed) {
  const std::string kHead = std::string(
                                "module t;\n"
                                "  logic a, b = 0, cc = 1;\n") +
                            kSay +
                            "  function bit fn(bit v);\n"
                            "    p: assert #0 (v) say(\"p pass\");\n"
                            "    else say(\"p fail\");\n"
                            "    return v;\n"
                            "  endfunction\n";
  const std::string kChange = "  initial begin #0 b = 1; cc = 0; end\n";
  EXPECT_EQ(Captured(kHead + "  always_comb a = b || fn(cc);\n" + kChange +
                     "endmodule\n"),
            "");
  EXPECT_EQ(Captured(kHead + "  always_comb a = b | fn(cc);\n" + kChange +
                     "endmodule\n"),
            "0 p fail\n");
  EXPECT_EQ(Captured(kHead + "  always_comb a = b || fn(cc);\nendmodule\n"),
            "0 p pass\n");
}

TEST(DeferredFlushPointsLive, TheTimeDelayExampleReportsA3AndFlushesA4) {
  EXPECT_EQ(Captured(std::string("module t;\n  logic a = 0, b = 0;\n") + kSay +
                     "  always @(a or b) begin : b1\n"
                     "    a3: assert #0 (a == b) say(\"a3 pass\");\n"
                     "    else say($sformatf(\"a3 fail a=%0d b=%0d\", a, b));\n"
                     "    #1;\n"
                     "    a4: assert #0 (a == b) say(\"a4 pass\");\n"
                     "    else say(\"a4 fail\");\n"
                     "  end\n"
                     "  initial begin\n"
                     "    #2 a = 1;\n"
                     "    #1;\n"
                     "    #0 b = 1;\n"
                     "  end\n"
                     "endmodule\n"),
            "2 a3 fail a=1 b=0\n3 a3 pass\n4 a4 pass\n");
}

TEST(DeferredFlushPointsLive, AResumeWithoutAnEventOrWaitSuspensionReports) {
  const Resume kCases[] = {
      {"", "    wait fork;\n"}, {"", "    #0;\n"},
      {"", "    y = #0 d;\n"},  {"  initial #0 -> e;\n", "    y <= @(e) d;\n"},
      {"", "    y <= #0 d;\n"},
  };
  for (const auto& r : kCases) {
    EXPECT_EQ(Captured(AroundTheInitial(
                  r.items, std::string("    assert #0 (0) else "
                                       "say(\"reported\");\n") +
                               r.body + "    say(\"resumed\");\n")),
              "0 resumed\n0 reported\n")
        << r.body;
  }
}

}  // namespace
