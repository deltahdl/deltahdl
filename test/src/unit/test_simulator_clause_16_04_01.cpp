#include <gtest/gtest.h>

#include <cstdint>
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

namespace {

struct DeferredFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

TEST(AssertionStatementSim, DeferredAssertHash0) {
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

TEST(DeferredAssertionReporting, ActionNotExecutedImmediatelyOnQueue) {
  DeferredFixture f;
  int pass_calls = 0;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&pass_calls]() { ++pass_calls; };

  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  EXPECT_EQ(pass_calls, 0);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredAssertionReporting, ObservedReportMaturesInObservedRegion) {
  DeferredFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 0u);
  f.engine.MatureObservedReports("p0");
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);
}

TEST(DeferredAssertionReporting, MaturedObservedSchedulesInReactiveAndClears) {
  DeferredFixture f;
  int pass_calls = 0;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&pass_calls]() { ++pass_calls; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.MatureObservedReports("p0");
  uint32_t scheduled =
      f.engine.ExecuteMaturedObservedInReactive("p0", f.scheduler, SimTime{0});
  EXPECT_EQ(scheduled, 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);

  f.scheduler.Run();
  EXPECT_EQ(pass_calls, 1);
}

TEST(DeferredAssertionReporting, MaturedReportSurvivesFlush) {
  DeferredFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.MatureObservedReports("p0");
  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredAssertionReporting, FinalReportMaturesInPostponed) {
  DeferredFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kFinal);

  f.engine.MatureFinalReports("p0");
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);
}

TEST(DeferredAssertionReporting,
     FinalActionScheduledInPostponedRegionAndClears) {
  DeferredFixture f;
  int fail_calls = 0;

  DeferredAssertion da;
  da.condition_val = 0;
  da.fail_action = [&fail_calls]() { ++fail_calls; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kFinal);

  f.engine.MatureFinalReports("p0");
  uint32_t scheduled =
      f.engine.ExecuteMaturedFinalInPostponed("p0", f.scheduler, SimTime{0});
  EXPECT_EQ(scheduled, 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);

  f.scheduler.Run();
  EXPECT_EQ(fail_calls, 1);
}

TEST(DeferredAssertionReporting, ObservedMaturationIgnoresFinalReports) {
  DeferredFixture f;
  DeferredAssertion da_obs;
  DeferredAssertion da_fin;
  da_obs.condition_val = 1;
  da_fin.condition_val = 1;
  f.engine.QueuePendingReport("p0", da_obs, DeferralKind::kObserved);
  f.engine.QueuePendingReport("p0", da_fin, DeferralKind::kFinal);

  f.engine.MatureObservedReports("p0");
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);
}

TEST(DeferredAssertionReporting, PerProcessQueuesAreIsolated) {
  DeferredFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("alpha", da, DeferralKind::kObserved);
  f.engine.QueuePendingReport("beta", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alpha", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alpha").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("beta").Size(), 1u);
}

TEST(DeferredAssertionReporting, FailingAssertWithoutElseUsesErrorFallback) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = false;
  da.kind = AssertionKind::kAssert;
  EXPECT_TRUE(UsesErrorSeverityFallback(da));
}

TEST(DeferredAssertionReporting, CoverDoesNotUseErrorFallback) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.has_else_clause = false;
  da.kind = AssertionKind::kCover;
  EXPECT_FALSE(UsesErrorSeverityFallback(da));
}

TEST(DeferredAssertionReporting, PassingAssertDoesNotUseErrorFallback) {
  DeferredAssertion da;
  da.condition_val = 1;
  da.has_else_clause = false;
  EXPECT_FALSE(UsesErrorSeverityFallback(da));
}

TEST(DeferredAssertionReporting, QueuedActionUsesArgValuesAtQueueTime) {
  DeferredFixture f;
  uint64_t live_arg = 7;
  uint64_t captured = 0;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [snapshot = live_arg, &captured]() { captured = snapshot; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  live_arg = 999;

  f.engine.MatureObservedReports("p0");
  f.engine.ExecuteMaturedObservedInReactive("p0", f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(captured, 7u);
}

TEST(DeferredAssertionReporting, FlushedPendingReportIsClearedAndNotExecuted) {
  DeferredFixture f;
  int pass_calls = 0;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&pass_calls]() { ++pass_calls; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);

  f.engine.MatureObservedReports("p0");
  uint32_t scheduled =
      f.engine.ExecuteMaturedObservedInReactive("p0", f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(scheduled, 0u);
  EXPECT_EQ(pass_calls, 0);
}

TEST(DeferredAssertionReporting, UnmaturedObservedDoesNotScheduleInReactive) {
  DeferredFixture f;
  int pass_calls = 0;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&pass_calls]() { ++pass_calls; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  uint32_t scheduled =
      f.engine.ExecuteMaturedObservedInReactive("p0", f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(scheduled, 0u);
  EXPECT_EQ(pass_calls, 0);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredAssertionReporting, UnmaturedFinalDoesNotScheduleInPostponed) {
  DeferredFixture f;
  int fail_calls = 0;

  DeferredAssertion da;
  da.condition_val = 0;
  da.fail_action = [&fail_calls]() { ++fail_calls; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kFinal);

  uint32_t scheduled =
      f.engine.ExecuteMaturedFinalInPostponed("p0", f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(scheduled, 0u);
  EXPECT_EQ(fail_calls, 0);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredAssertionReporting, FinalPendingReportIsClearedByFlushPoint) {
  DeferredFixture f;
  int fail_calls = 0;

  DeferredAssertion da;
  da.condition_val = 0;
  da.fail_action = [&fail_calls]() { ++fail_calls; };
  f.engine.QueuePendingReport("p0", da, DeferralKind::kFinal);
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);

  f.engine.MatureFinalReports("p0");
  uint32_t scheduled =
      f.engine.ExecuteMaturedFinalInPostponed("p0", f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(scheduled, 0u);
  EXPECT_EQ(fail_calls, 0);
}

}  // namespace
