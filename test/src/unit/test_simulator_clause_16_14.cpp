// §16.14: Concurrent assertions

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/sim_context.h"

using namespace delta;


struct AssertionSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
namespace {

// =============================================================================
// AssertionMonitor basics
// =============================================================================
TEST(Assertion, AddPropertyAndCount) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "clk";
  monitor.AddProperty(prop);
  EXPECT_EQ(monitor.PropertyCount(), 1u);
}

TEST(Assertion, AttachEvaluatesOnSignalChange) {
  AssertionSimFixture f;
  auto* sig = f.ctx.CreateVariable("sig", 1);
  sig->value = MakeLogic4VecVal(f.arena, 1, 0);

  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Attach(f.ctx, f.scheduler);

  // Schedule: at t=0 set sig=0 (init), at t=10 set sig=1.
  auto* ev0 = f.scheduler.GetEventPool().Acquire();
  ev0->callback = [&sig, &f]() {
    sig->value = MakeLogic4VecVal(f.arena, 1, 0);
    sig->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{0}, Region::kActive, ev0);

  auto* ev1 = f.scheduler.GetEventPool().Acquire();
  ev1->callback = [&sig, &f]() {
    sig->value = MakeLogic4VecVal(f.arena, 1, 1);
    sig->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev1);

  f.scheduler.Run();

  // The $rose assertion should have detected 0→1.
  EXPECT_GE(monitor.PassCount(), 1u);
}

TEST(Assertion, AttachDetectsFailure) {
  AssertionSimFixture f;
  auto* sig = f.ctx.CreateVariable("sig", 32);
  sig->value = MakeLogic4VecVal(f.arena, 32, 5);

  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_stable";
  prop.kind = SvaPropertyKind::kStable;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Attach(f.ctx, f.scheduler);

  auto* ev0 = f.scheduler.GetEventPool().Acquire();
  ev0->callback = [&sig, &f]() {
    sig->value = MakeLogic4VecVal(f.arena, 32, 5);
    sig->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{0}, Region::kActive, ev0);

  auto* ev1 = f.scheduler.GetEventPool().Acquire();
  ev1->callback = [&sig, &f]() {
    sig->value = MakeLogic4VecVal(f.arena, 32, 10);
    sig->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev1);

  f.scheduler.Run();

  EXPECT_GE(monitor.FailCount(), 1u);
}

}  // namespace
