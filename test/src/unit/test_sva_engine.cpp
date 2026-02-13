#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/sva_engine.h"

using namespace delta;

// =============================================================================
// Test fixture
// =============================================================================

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

// =============================================================================
// SequenceAttempt basics
// =============================================================================

TEST(SvaEngine, SequenceAttemptDefaultState) {
  SequenceAttempt sa;
  EXPECT_EQ(sa.position, 0u);
  EXPECT_EQ(sa.delay_remaining, 0u);
  EXPECT_EQ(sa.match_count, 0u);
  EXPECT_FALSE(sa.completed);
  EXPECT_FALSE(sa.failed);
}

TEST(SvaEngine, SequenceAttemptDelayCountdown) {
  SequenceAttempt sa;
  sa.delay_remaining = 3;
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 2u);
  EXPECT_FALSE(sa.completed);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 1u);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 0u);
}

// =============================================================================
// Sequence delay ##N (section 16.9)
// =============================================================================

TEST(SvaEngine, SequenceDelaySimple) {
  SvaFixture f;
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  SequenceAttempt sa;
  sa.delay_remaining = 2;
  AdvanceSequence(sa);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 0u);
}

TEST(SvaEngine, SequenceDelayZero) {
  SequenceAttempt sa;
  sa.delay_remaining = 0;
  AdvanceSequence(sa);
  // Zero delay: still at 0.
  EXPECT_EQ(sa.delay_remaining, 0u);
}

// =============================================================================
// Sequence repetition [*N] (section 16.9.2)
// =============================================================================

TEST(SvaEngine, ConsecutiveRepetitionExact) {
  SvaFixture f;
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Simulate 3 consecutive matches.
  auto result = MatchRepetition(seq, {1, 1, 1});
  EXPECT_TRUE(result);
}

TEST(SvaEngine, ConsecutiveRepetitionNotEnough) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Only 2 matches before a mismatch.
  auto result = MatchRepetition(seq, {1, 1, 0});
  EXPECT_FALSE(result);
}

TEST(SvaEngine, ConsecutiveRepetitionRange) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 4;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // 2 is within [2:4].
  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
  // 3 is within [2:4].
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1}));
  // 4 is within [2:4].
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1}));
  // 1 is below range.
  EXPECT_FALSE(MatchRepetition(seq, {1}));
}

// =============================================================================
// Goto repetition [->N] (section 16.9.4)
// =============================================================================

TEST(SvaEngine, GotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Two non-consecutive matches: 0,1,0,1.
  // Goto: match must end at the Nth match.
  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1}));
  // Only one match.
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 0}));
}

TEST(SvaEngine, GotoRepetitionEndsAtMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 1;
  seq.rep_max = 1;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Last element must be a match for goto repetition.
  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0}));
}

// =============================================================================
// Non-consecutive repetition [=N] (section 16.9.5)
// =============================================================================

TEST(SvaEngine, NonConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Two matches scattered: does not need to end at match.
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {0, 1, 0, 1, 0}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1}));
  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 0}));
}

// =============================================================================
// Sequence operators: and, or, intersect (section 16.9.6-8)
// =============================================================================

TEST(SvaEngine, SequenceOperatorAnd) {
  bool a_matched = true;
  bool b_matched = true;
  EXPECT_TRUE(EvalSequenceAnd(a_matched, b_matched));
  EXPECT_FALSE(EvalSequenceAnd(true, false));
  EXPECT_FALSE(EvalSequenceAnd(false, true));
  EXPECT_FALSE(EvalSequenceAnd(false, false));
}

TEST(SvaEngine, SequenceOperatorOr) {
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

TEST(SvaEngine, SequenceOperatorIntersect) {
  // Intersect: both match and complete at the same cycle.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 3, 3));
  // Different lengths: false.
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 3, 4));
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 3, 3));
}

// =============================================================================
// Sequence throughout (section 16.9.9)
// =============================================================================

TEST(SvaEngine, SequenceThroughout) {
  // expr must hold throughout the entire sequence.
  std::vector<uint64_t> values = {1, 1, 1, 1};
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));

  values = {1, 1, 0, 1};
  EXPECT_FALSE(EvalThroughout(check, values));
}

TEST(SvaEngine, SequenceThroughoutEmpty) {
  std::vector<uint64_t> values;
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));
}

// =============================================================================
// Property implication |-> and |=> (section 16.12.7)
// =============================================================================

TEST(SvaEngine, OverlappingImplication) {
  // |-> : if antecedent matches, consequent must match at the same cycle.
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);
  // Antecedent false => vacuous pass.
  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
}

TEST(SvaEngine, NonOverlappingImplication) {
  // |=> : if antecedent matches, consequent is checked on next cycle.
  // When non_overlapping=true and antecedent matches, result is kPending.
  EXPECT_EQ(EvalImplication(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
}

// =============================================================================
// Property temporal operators: not, and, or (section 16.12.8-10)
// =============================================================================

TEST(SvaEngine, PropertyNot) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

TEST(SvaEngine, PropertyAnd) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(SvaEngine, PropertyOr) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

// =============================================================================
// Assertion pass/fail action blocks (section 16.5)
// =============================================================================

TEST(SvaEngine, PassActionBlockInvoked) {
  SvaFixture f;
  bool pass_called = false;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 1;  // Passes.
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
  da.condition_val = 0;  // Fails.
  da.pass_action = [&pass_called]() { pass_called = true; };
  da.fail_action = [&fail_called]() { fail_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_FALSE(pass_called);
  EXPECT_TRUE(fail_called);
}

TEST(SvaEngine, NoActionBlockDoesNotCrash) {
  DeferredAssertion da;
  da.condition_val = 0;
  // No actions set, should not crash.
  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(true);
}

// =============================================================================
// Deferred immediate assertions with #0 (section 16.4)
// =============================================================================

TEST(SvaEngine, DeferredAssertionScheduledInObserved) {
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});

  // Must be scheduled in Observed region.
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

// =============================================================================
// AssertionControl: $assertoff/$asserton/$assertkill (section 16.13)
// =============================================================================

TEST(SvaEngine, AssertionControlDefaultOn) {
  AssertionControl ctrl;
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsEnabled("inst2"));
}

TEST(SvaEngine, AssertoffDisablesInstance) {
  AssertionControl ctrl;
  ctrl.SetOff("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsEnabled("inst2"));
}

TEST(SvaEngine, AssertonReenablesInstance) {
  AssertionControl ctrl;
  ctrl.SetOff("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  ctrl.SetOn("inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
}

TEST(SvaEngine, AssertkillKillsAndDisables) {
  AssertionControl ctrl;
  ctrl.Kill("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.WasKilled("inst1"));
}

// =============================================================================
// $assertcontrol, $assertpassoff, $assertfailon (section 16.13)
// =============================================================================

TEST(SvaEngine, AssertControlGlobalOff) {
  AssertionControl ctrl;
  ctrl.SetGlobalOff();
  EXPECT_FALSE(ctrl.IsEnabled("any_instance"));
  EXPECT_FALSE(ctrl.IsEnabled("another_inst"));
}

TEST(SvaEngine, AssertControlGlobalOn) {
  AssertionControl ctrl;
  ctrl.SetGlobalOff();
  ctrl.SetGlobalOn();
  EXPECT_TRUE(ctrl.IsEnabled("any_instance"));
}

TEST(SvaEngine, AssertPassOff) {
  AssertionControl ctrl;
  EXPECT_TRUE(ctrl.IsPassEnabled("inst1"));
  ctrl.SetPassOff("inst1");
  EXPECT_FALSE(ctrl.IsPassEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsPassEnabled("inst2"));
}

TEST(SvaEngine, AssertFailOn) {
  AssertionControl ctrl;
  ctrl.SetFailOff("inst1");
  EXPECT_FALSE(ctrl.IsFailEnabled("inst1"));
  ctrl.SetFailOn("inst1");
  EXPECT_TRUE(ctrl.IsFailEnabled("inst1"));
}

// =============================================================================
// Concurrent assertion disable iff (section 16.12.5)
// =============================================================================

TEST(SvaEngine, DisableIffTrue) {
  // When disable condition is true, assertion is vacuously passed.
  PropertyResult result = EvalWithDisableIff(true, PropertyResult::kFail);
  EXPECT_EQ(result, PropertyResult::kVacuousPass);
}

TEST(SvaEngine, DisableIffFalse) {
  // When disable condition is false, assertion result is unchanged.
  PropertyResult result = EvalWithDisableIff(false, PropertyResult::kFail);
  EXPECT_EQ(result, PropertyResult::kFail);
}

TEST(SvaEngine, DisableIffFalsePass) {
  PropertyResult result = EvalWithDisableIff(false, PropertyResult::kPass);
  EXPECT_EQ(result, PropertyResult::kPass);
}

// =============================================================================
// Assertion severity levels ($fatal, $error, $warning, $info)
// =============================================================================

TEST(SvaEngine, SeverityLevelValues) {
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kInfo), 0);
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kWarning), 1);
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kError), 2);
  EXPECT_EQ(static_cast<int>(AssertionSeverity::kFatal), 3);
}

TEST(SvaEngine, SeverityToString) {
  EXPECT_EQ(SeverityToString(AssertionSeverity::kInfo), "INFO");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kWarning), "WARNING");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kError), "ERROR");
  EXPECT_EQ(SeverityToString(AssertionSeverity::kFatal), "FATAL");
}

TEST(SvaEngine, SeverityDefaultIsError) {
  AssertionSeverity sev = AssertionSeverity::kError;
  EXPECT_EQ(SeverityToString(sev), "ERROR");
}

// =============================================================================
// SvaEngine integration tests
// =============================================================================

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

TEST(SvaEngine, AssertionControlIntegration) {
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "my_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.GetControl().SetOff("my_assert");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(executed);
}

TEST(SvaEngine, AssertionControlEnabledExecution) {
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "my_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(executed);
}

// =============================================================================
// Sequence matching complete patterns
// =============================================================================

TEST(SvaEngine, DelaySequenceMatchFull) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 2;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  // Values: cycle0=1, delay 2, cycle2 check.
  std::vector<uint64_t> vals = {1, 0, 1};
  EXPECT_TRUE(MatchDelaySequence(seq, vals));
}

TEST(SvaEngine, DelaySequenceNoMatchAtEnd) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 1;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  std::vector<uint64_t> vals = {1, 0};
  EXPECT_FALSE(MatchDelaySequence(seq, vals));
}

TEST(SvaEngine, PropertyPendingResolvesPass) {
  // Simulate |=> with pass on next cycle.
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  // Next cycle consequent matches.
  auto resolved = ResolveNonOverlapping(true);
  EXPECT_EQ(resolved, PropertyResult::kPass);
}

TEST(SvaEngine, PropertyPendingResolvesFail) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(false);
  EXPECT_EQ(resolved, PropertyResult::kFail);
}

// =============================================================================
// Edge cases and robustness
// =============================================================================

TEST(SvaEngine, RepetitionZeroMin) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 0;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Zero matches is valid when min is 0.
  EXPECT_TRUE(MatchRepetition(seq, {}));
  EXPECT_TRUE(MatchRepetition(seq, {1}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
}

TEST(SvaEngine, PassOffSkipsPassAction) {
  SvaFixture f;
  bool pass_called = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "check_a";
  da.pass_action = [&pass_called]() { pass_called = true; };

  f.engine.GetControl().SetPassOff("check_a");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertionsRespectingControl(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(pass_called);
}

TEST(SvaEngine, FailOffSkipsFailAction) {
  SvaFixture f;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "check_b";
  da.fail_action = [&fail_called]() { fail_called = true; };

  f.engine.GetControl().SetFailOff("check_b");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertionsRespectingControl(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(fail_called);
}

TEST(SvaEngine, KillClearsPendingAssertions) {
  SvaFixture f;
  int count = 0;

  for (int i = 0; i < 3; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.instance_name = "killed_inst";
    da.pass_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }

  f.engine.KillAssertionsForInstance("killed_inst");
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);
}
