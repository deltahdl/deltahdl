// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/sim_context.h"

using namespace delta;

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

TEST(Assertion, RoseDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  // First evaluation: cycle_count==0, vacuous pass (initializes prev).
  auto r0 = monitor.Evaluate("p_rose", 0);
  EXPECT_EQ(r0, AssertionResult::kVacuousPass);

  // Simulate one tick to advance cycle count.
  // We need a SimContext, but Tick just increments cycle_count.
  // Use a minimal approach: manually increment via a second Evaluate.
  // Actually, we need to call Tick. Let's hack around it by
  // constructing a dummy approach. For the test we'll directly
  // modify the entry cycle count by calling Evaluate after AddProperty.
  // The first Evaluate set prev_value=0, cycle_count was 0.
  // Now "tick" it:
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose"));
  ASSERT_NE(entry, nullptr);
  entry->cycle_count = 1;

  // 0 -> 1 is a rising edge.
  auto r1 = monitor.Evaluate("p_rose", 1);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  // 1 -> 1 is NOT a rising edge.
  auto r2 = monitor.Evaluate("p_rose", 1);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

TEST(Assertion, FellDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  // Initialize: prev_value = 1.
  monitor.Evaluate("p_fell", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell"));
  entry->cycle_count = 1;

  // 1 -> 0 is a falling edge.
  auto r1 = monitor.Evaluate("p_fell", 0);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  // 0 -> 0 is NOT a falling edge.
  auto r2 = monitor.Evaluate("p_fell", 0);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

TEST(Assertion, StableDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_stable";
  prop.kind = SvaPropertyKind::kStable;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_stable", 42);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_stable"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_stable", 42);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  auto r2 = monitor.Evaluate("p_stable", 99);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

TEST(Assertion, CustomCheckFunction) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_custom";
  prop.kind = SvaPropertyKind::kCustom;
  prop.signal_name = "sig";
  // Custom: current must be greater than previous.
  prop.custom_check = [](uint64_t cur, uint64_t prev) { return cur > prev; };
  monitor.AddProperty(prop);

  monitor.Evaluate("p_custom", 10);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_custom"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_custom", 20);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  auto r2 = monitor.Evaluate("p_custom", 5);
  EXPECT_EQ(r2, AssertionResult::kFail);
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

// =============================================================================
// §16.9.3: $changed — assertion monitor support
// =============================================================================
TEST(Assertion, ChangedDetected) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  // Initialize: prev_value = 5.
  monitor.Evaluate("p_changed", 5);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed"));
  entry->cycle_count = 1;

  // 5 -> 7 is a change → kPass.
  auto r1 = monitor.Evaluate("p_changed", 7);
  EXPECT_EQ(r1, AssertionResult::kPass);
}

TEST(Assertion, ChangedStable) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed2";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed2", 42);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed2"));
  entry->cycle_count = 1;

  // 42 -> 42 is NOT a change → kFail.
  auto r1 = monitor.Evaluate("p_changed2", 42);
  EXPECT_EQ(r1, AssertionResult::kFail);
}

}
TEST(Assertion, LetWithPastInBody) {
  SampledLetFixture f;
  // let get_past(x) = $past(x);
  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$past", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_past", body, {arg});
  f.ctx.RegisterLetDecl("get_past", decl);

  // Create variable sig = 42.
  auto* var = f.ctx.CreateVariable("sig", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 42);

  // get_past(sig) → let expansion → $past(x) with x=42 → stub returns 42.
  auto* call = SLMakeCall(f.arena, "get_past", {SLMakeId(f.arena, "sig")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Assertion, LetWithChangedInBody) {
  SampledLetFixture f;
  // let check_changed(x) = $changed(x);
  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$changed", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "check_changed", body, {arg});
  f.ctx.RegisterLetDecl("check_changed", decl);

  auto* var = f.ctx.CreateVariable("sig2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);

  // check_changed(sig2) → let expansion → $changed(x) with x=5 → stub returns
  // 0.
  auto* call =
      SLMakeCall(f.arena, "check_changed", {SLMakeId(f.arena, "sig2")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Assertion, LetWithSampledInBody) {
  SampledLetFixture f;
  // let get_sampled(x) = $sampled(x);
  FunctionArg arg;
  arg.name = "x";
  auto* body = SLMakeSysCall(f.arena, "$sampled", {SLMakeId(f.arena, "x")});
  auto* decl = SLMakeLetDecl(f.arena, "get_sampled", body, {arg});
  f.ctx.RegisterLetDecl("get_sampled", decl);

  auto* var = f.ctx.CreateVariable("sig3", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  // get_sampled(sig3) → let expansion → $sampled(x) with x=99 → returns 99.
  auto* call = SLMakeCall(f.arena, "get_sampled", {SLMakeId(f.arena, "sig3")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

}  // namespace
