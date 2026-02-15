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

struct SimCh16Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

// =============================================================================
// assert property: simple boolean pass/fail (section 16.5.1)
// =============================================================================

TEST(SimCh16, AssertPropertySimpleBooleanPass) {
  // A concurrent assert with a true boolean expression passes.
  SimCh16Fixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "assert_bool_pass";

  bool pass_invoked = false;
  da.pass_action = [&pass_invoked]() { pass_invoked = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(pass_invoked);
}

TEST(SimCh16, AssertPropertySimpleBooleanFail) {
  // A concurrent assert with a false boolean expression fails.
  SimCh16Fixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "assert_bool_fail";

  bool fail_invoked = false;
  da.fail_action = [&fail_invoked]() { fail_invoked = true; };

  f.engine.QueueDeferredAssertion(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(fail_invoked);
}

// =============================================================================
// assert property with pass/fail action blocks (section 16.5.1)
// =============================================================================

TEST(SimCh16, AssertPropertyWithPassActionBlock) {
  // Pass action block is invoked when assertion passes.
  DeferredAssertion da;
  da.condition_val = 1;
  int pass_count = 0;
  da.pass_action = [&pass_count]() { ++pass_count; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_EQ(pass_count, 1);
}

TEST(SimCh16, AssertPropertyWithFailActionBlock) {
  // Fail action block is invoked when assertion fails.
  DeferredAssertion da;
  da.condition_val = 0;
  int fail_count = 0;
  da.fail_action = [&fail_count]() { ++fail_count; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_EQ(fail_count, 1);
}

TEST(SimCh16, AssertPropertyWithBothPassAndFailActions) {
  // Only the pass action runs on pass; only the fail action runs on fail.
  bool pass_called = false;
  bool fail_called = false;

  DeferredAssertion da_pass;
  da_pass.condition_val = 1;
  da_pass.pass_action = [&pass_called]() { pass_called = true; };
  da_pass.fail_action = [&fail_called]() { fail_called = true; };
  ExecuteDeferredAssertionAction(da_pass);
  EXPECT_TRUE(pass_called);
  EXPECT_FALSE(fail_called);

  pass_called = false;
  fail_called = false;

  DeferredAssertion da_fail;
  da_fail.condition_val = 0;
  da_fail.pass_action = [&pass_called]() { pass_called = true; };
  da_fail.fail_action = [&fail_called]() { fail_called = true; };
  ExecuteDeferredAssertionAction(da_fail);
  EXPECT_FALSE(pass_called);
  EXPECT_TRUE(fail_called);
}

// =============================================================================
// assume property (section 16.5.1)
// =============================================================================

TEST(SimCh16, AssumePropertySimplePass) {
  // assume property behaves like assert for simulation: pass action fires.
  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "assume_pass";
  bool pass_called = false;
  da.pass_action = [&pass_called]() { pass_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(pass_called);
}

TEST(SimCh16, AssumePropertySimpleFail) {
  // assume property fail: fail action fires.
  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "assume_fail";
  bool fail_called = false;
  da.fail_action = [&fail_called]() { fail_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(fail_called);
}

// =============================================================================
// cover property (section 16.5.1)
// =============================================================================

TEST(SimCh16, CoverPropertyMatchTriggersAction) {
  // cover property: when the property matches, the action block executes.
  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "cover_match";
  bool action_called = false;
  da.pass_action = [&action_called]() { action_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(action_called);
}

TEST(SimCh16, CoverPropertyNoMatchNoAction) {
  // cover property: when the property does not match, the action block is
  // not executed (cover has no fail action).
  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "cover_no_match";
  bool action_called = false;
  // Cover property only has a pass action, no fail action.
  da.pass_action = [&action_called]() { action_called = true; };

  ExecuteDeferredAssertionAction(da);
  // Condition failed, so pass_action is not called.
  EXPECT_FALSE(action_called);
}

// =============================================================================
// Overlapping and non-overlapping implication (section 16.5.1 / 16.12.7)
// =============================================================================

TEST(SimCh16, AssertPropertyOverlappingImplication) {
  // |-> : consequent checked at same cycle as antecedent match.
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);
}

TEST(SimCh16, AssertPropertyNonOverlappingImplication) {
  // |=> : consequent checked on next cycle (kPending when antecedent matches).
  auto result = EvalImplication(true, false, true);
  EXPECT_EQ(result, PropertyResult::kPending);

  // Resolve on next cycle: consequent matches -> pass.
  EXPECT_EQ(ResolveNonOverlapping(true), PropertyResult::kPass);
  // Resolve on next cycle: consequent fails -> fail.
  EXPECT_EQ(ResolveNonOverlapping(false), PropertyResult::kFail);
}

// =============================================================================
// Vacuous pass when antecedent is false (section 16.5.1 / 16.12.7)
// =============================================================================

TEST(SimCh16, AssertPropertyVacuousPassAntecedentFalse) {
  // When the antecedent of an implication is false, the assertion vacuously
  // passes regardless of the consequent, for both |-> and |=>.
  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, true), PropertyResult::kVacuousPass);
}

// =============================================================================
// disable iff (section 16.5.1 / 16.12.5)
// =============================================================================

TEST(SimCh16, AssertPropertyDisableIffConditionTrue) {
  // When the disable condition is true, the assertion is vacuously passed
  // regardless of the inner property result.
  EXPECT_EQ(EvalWithDisableIff(true, PropertyResult::kFail),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalWithDisableIff(true, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
}

TEST(SimCh16, AssertPropertyDisableIffConditionFalse) {
  // When the disable condition is false, the inner property result is returned.
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

// =============================================================================
// Sequence delay ##N (section 16.5.1 / 16.9)
// =============================================================================

TEST(SimCh16, AssertPropertySequenceDelay) {
  // ##N delay: expression evaluated after N clock ticks.
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 3;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  // After 3 cycles of delay, the 4th value is the check target.
  // vals[0] is the trigger, vals[3] is checked.
  std::vector<uint64_t> vals_pass = {1, 0, 0, 1};
  EXPECT_TRUE(MatchDelaySequence(seq, vals_pass));

  std::vector<uint64_t> vals_fail = {1, 0, 0, 0};
  EXPECT_FALSE(MatchDelaySequence(seq, vals_fail));
}

// =============================================================================
// Consecutive repetition [*N] (section 16.5.1 / 16.9.2)
// =============================================================================

TEST(SimCh16, AssertPropertyConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 4;
  seq.rep_max = 4;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Exactly 4 consecutive matches.
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1}));
  // 3 consecutive then a miss.
  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1, 0}));
  // Too few values.
  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1}));
}

// =============================================================================
// Goto repetition [->N] (section 16.5.1 / 16.9.4)
// =============================================================================

TEST(SimCh16, AssertPropertyGotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // 3 matches with gaps; last value must be a match (goto semantics).
  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1, 0, 1}));
  // Last value is not a match.
  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0, 1, 0}));
  // Only 2 matches total.
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 1}));
}

// =============================================================================
// Non-consecutive repetition [=N] (section 16.5.1 / 16.9.5)
// =============================================================================

TEST(SimCh16, AssertPropertyNonConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // 3 scattered matches; need not end at a match.
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 1, 0}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 1, 1}));
  // Only 2 matches.
  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 0}));
}

// =============================================================================
// Property not operator (section 16.5.1 / 16.12.8)
// =============================================================================

TEST(SimCh16, PropertyNotOperator) {
  // not inverts pass to fail and vice versa.
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
  // Vacuous pass under not becomes fail per LRM.
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

// =============================================================================
// Property and operator (section 16.5.1 / 16.12.9)
// =============================================================================

TEST(SimCh16, PropertyAndOperator) {
  // Both must pass for the result to be pass.
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  // Any fail causes overall fail.
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

// =============================================================================
// Property or operator (section 16.5.1 / 16.12.10)
// =============================================================================

TEST(SimCh16, PropertyOrOperator) {
  // Either pass causes overall pass.
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
  // Both fail causes overall fail.
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

// =============================================================================
// Sequence and operator (section 16.5.1 / 16.9.6)
// =============================================================================

TEST(SimCh16, SequenceAndOperator) {
  // Both sequences must match for the compound sequence to match.
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceAnd(true, false));
  EXPECT_FALSE(EvalSequenceAnd(false, true));
  EXPECT_FALSE(EvalSequenceAnd(false, false));
}

// =============================================================================
// Sequence or operator (section 16.5.1 / 16.9.7)
// =============================================================================

TEST(SimCh16, SequenceOrOperator) {
  // Either sequence matching causes the compound sequence to match.
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

// =============================================================================
// Sequence intersect operator (section 16.5.1 / 16.9.8)
// =============================================================================

TEST(SimCh16, SequenceIntersectOperator) {
  // Intersect: both sequences match and complete at the same length.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 5, 5));
  // Different lengths: no match even if both matched.
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 5, 6));
  // One sequence did not match.
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, true, 5, 5));
}

// =============================================================================
// Sequence throughout operator (section 16.5.1 / 16.9.9)
// =============================================================================

TEST(SimCh16, SequenceThroughoutOperator) {
  // Expression must hold at every cycle throughout the sequence.
  auto check = [](uint64_t v) { return v != 0; };
  EXPECT_TRUE(EvalThroughout(check, {1, 2, 3, 4}));
  // Failure at one cycle causes the overall result to fail.
  EXPECT_FALSE(EvalThroughout(check, {1, 0, 3, 4}));
  // Empty sequence is trivially satisfied.
  EXPECT_TRUE(EvalThroughout(check, {}));
}

// =============================================================================
// Multiple concurrent assertions queued and flushed (section 16.5.1)
// =============================================================================

TEST(SimCh16, MultipleConcurrentAssertionsQueuedAndFlushed) {
  SimCh16Fixture f;
  int pass_count = 0;
  int fail_count = 0;

  // Queue several assertions with mixed pass/fail conditions.
  for (int i = 0; i < 4; ++i) {
    DeferredAssertion da;
    da.condition_val = (i % 2 == 0) ? 1 : 0;
    da.instance_name = "multi_assert_" + std::to_string(i);
    da.pass_action = [&pass_count]() { ++pass_count; };
    da.fail_action = [&fail_count]() { ++fail_count; };
    f.engine.QueueDeferredAssertion(da);
  }

  EXPECT_EQ(f.engine.DeferredQueueSize(), 4u);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);
  f.scheduler.Run();

  // Indices 0, 2 pass; indices 1, 3 fail.
  EXPECT_EQ(pass_count, 2);
  EXPECT_EQ(fail_count, 2);
}

// =============================================================================
// Assertion control: $assertoff (section 16.5.1 / 16.13)
// =============================================================================

TEST(SimCh16, AssertionControlAssertoffDisablesAssertion) {
  SimCh16Fixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "disabled_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.GetControl().SetOff("disabled_assert");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(executed);
  EXPECT_FALSE(f.engine.GetControl().IsEnabled("disabled_assert"));
}

// =============================================================================
// Assertion control: $asserton (section 16.5.1 / 16.13)
// =============================================================================

TEST(SimCh16, AssertionControlAssertonReenablesAssertion) {
  SimCh16Fixture f;
  bool executed = false;

  f.engine.GetControl().SetOff("reenable_assert");
  EXPECT_FALSE(f.engine.GetControl().IsEnabled("reenable_assert"));

  f.engine.GetControl().SetOn("reenable_assert");
  EXPECT_TRUE(f.engine.GetControl().IsEnabled("reenable_assert"));

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "reenable_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(executed);
}

// =============================================================================
// Assertion control: $assertkill (section 16.5.1 / 16.13)
// =============================================================================

TEST(SimCh16, AssertionControlAssertkillRemovesPendingAssertions) {
  SimCh16Fixture f;
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.instance_name = "kill_target";
    da.pass_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }

  EXPECT_EQ(f.engine.DeferredQueueSize(), 5u);
  f.engine.KillAssertionsForInstance("kill_target");
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);

  // The instance is also marked as killed.
  EXPECT_TRUE(f.engine.GetControl().WasKilled("kill_target"));
}

// =============================================================================
// Deferred assertion (#0) executed in Observed region (section 16.5.1 / 16.4)
// =============================================================================

TEST(SimCh16, DeferredAssertionExecutedInObservedRegion) {
  SimCh16Fixture f;
  bool observed_executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "deferred_observed";
  da.pass_action = [&observed_executed]() { observed_executed = true; };

  f.engine.QueueDeferredAssertion(da);
  // FlushDeferredAssertions schedules execution in the Observed region.
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});

  // Before running the scheduler, the action has not yet executed.
  EXPECT_FALSE(observed_executed);

  // Running the scheduler processes the Observed region.
  f.scheduler.Run();
  EXPECT_TRUE(observed_executed);
}
