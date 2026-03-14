#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

struct SimCh16Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

TEST(ConcurrentAssertionSim, AssertPropertySimpleBooleanPass) {
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

TEST(ConcurrentAssertionSim, AssertPropertySimpleBooleanFail) {
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

TEST(ConcurrentAssertionSim, AssertPropertyWithPassActionBlock) {
  DeferredAssertion da;
  da.condition_val = 1;
  int pass_count = 0;
  da.pass_action = [&pass_count]() { ++pass_count; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_EQ(pass_count, 1);
}

TEST(ConcurrentAssertionSim, AssertPropertyWithFailActionBlock) {
  DeferredAssertion da;
  da.condition_val = 0;
  int fail_count = 0;
  da.fail_action = [&fail_count]() { ++fail_count; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_EQ(fail_count, 1);
}

TEST(ConcurrentAssertionSim, AssertPropertyWithBothPassAndFailActions) {
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

TEST(ConcurrentAssertionSim, AssumePropertySimplePass) {
  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "assume_pass";
  bool pass_called = false;
  da.pass_action = [&pass_called]() { pass_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(pass_called);
}

TEST(ConcurrentAssertionSim, AssumePropertySimpleFail) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "assume_fail";
  bool fail_called = false;
  da.fail_action = [&fail_called]() { fail_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(fail_called);
}

TEST(ConcurrentAssertionSim, CoverPropertyMatchTriggersAction) {
  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "cover_match";
  bool action_called = false;
  da.pass_action = [&action_called]() { action_called = true; };

  ExecuteDeferredAssertionAction(da);
  EXPECT_TRUE(action_called);
}

TEST(ConcurrentAssertionSim, CoverPropertyNoMatchNoAction) {
  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "cover_no_match";
  bool action_called = false;

  da.pass_action = [&action_called]() { action_called = true; };

  ExecuteDeferredAssertionAction(da);

  EXPECT_FALSE(action_called);
}

TEST(ConcurrentAssertionSim, AssertPropertyOverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);
}

TEST(ConcurrentAssertionSim, AssertPropertyNonOverlappingImplication) {
  auto result = EvalImplication(true, false, true);
  EXPECT_EQ(result, PropertyResult::kPending);

  EXPECT_EQ(ResolveNonOverlapping(true), PropertyResult::kPass);

  EXPECT_EQ(ResolveNonOverlapping(false), PropertyResult::kFail);
}

TEST(ConcurrentAssertionSim, AssertPropertyVacuousPassAntecedentFalse) {
  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, true), PropertyResult::kVacuousPass);
}

TEST(ConcurrentAssertionSim, AssertPropertyDisableIffConditionTrue) {
  EXPECT_EQ(EvalWithDisableIff(true, PropertyResult::kFail),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalWithDisableIff(true, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
}

TEST(ConcurrentAssertionSim, AssertPropertyDisableIffConditionFalse) {
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

TEST(ConcurrentAssertionSim, AssertPropertySequenceDelay) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 3;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  std::vector<uint64_t> vals_pass = {1, 0, 0, 1};
  EXPECT_TRUE(MatchDelaySequence(seq, vals_pass));

  std::vector<uint64_t> vals_fail = {1, 0, 0, 0};
  EXPECT_FALSE(MatchDelaySequence(seq, vals_fail));
}

TEST(ConcurrentAssertionSim, AssertPropertyConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 4;
  seq.rep_max = 4;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1}));

  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1, 0}));

  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1}));
}

TEST(ConcurrentAssertionSim, AssertPropertyGotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1, 0, 1}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0, 1, 0}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 1}));
}

TEST(ConcurrentAssertionSim, AssertPropertyNonConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 1, 0}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 1, 1}));

  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 0}));
}

TEST(ConcurrentAssertionSim, PropertyNotOperator) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);

  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

TEST(ConcurrentAssertionSim, PropertyAndOperator) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);

  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(ConcurrentAssertionSim, PropertyOrOperator) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);

  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(ConcurrentAssertionSim, SequenceAndOperator) {
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceAnd(true, false));
  EXPECT_FALSE(EvalSequenceAnd(false, true));
  EXPECT_FALSE(EvalSequenceAnd(false, false));
}

TEST(ConcurrentAssertionSim, SequenceOrOperator) {
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

TEST(ConcurrentAssertionSim, SequenceIntersectOperator) {
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 5, 5));

  EXPECT_FALSE(EvalSequenceIntersect(true, true, 5, 6));

  EXPECT_FALSE(EvalSequenceIntersect(true, false, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, true, 5, 5));
}

TEST(ConcurrentAssertionSim, SequenceThroughoutOperator) {
  auto check = [](uint64_t v) { return v != 0; };
  EXPECT_TRUE(EvalThroughout(check, {1, 2, 3, 4}));

  EXPECT_FALSE(EvalThroughout(check, {1, 0, 3, 4}));

  EXPECT_TRUE(EvalThroughout(check, {}));
}

TEST(ConcurrentAssertionSim, MultipleConcurrentAssertionsQueuedAndFlushed) {
  SimCh16Fixture f;
  int pass_count = 0;
  int fail_count = 0;

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

  EXPECT_EQ(pass_count, 2);
  EXPECT_EQ(fail_count, 2);
}

TEST(ConcurrentAssertionSim, AssertionControlAssertoffDisablesAssertion) {
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

TEST(ConcurrentAssertionSim, AssertionControlAssertonReenablesAssertion) {
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

TEST(ConcurrentAssertionSim, AssertionControlAssertkillRemovesPendingAssertions) {
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

  EXPECT_TRUE(f.engine.GetControl().WasKilled("kill_target"));
}

TEST(ConcurrentAssertionSim, DeferredAssertionExecutedInObservedRegion) {
  SimCh16Fixture f;
  bool observed_executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "deferred_observed";
  da.pass_action = [&observed_executed]() { observed_executed = true; };

  f.engine.QueueDeferredAssertion(da);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});

  EXPECT_FALSE(observed_executed);

  f.scheduler.Run();
  EXPECT_TRUE(observed_executed);
}
