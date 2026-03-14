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

TEST(SimCh16, AssertPropertyOverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);
}

TEST(SimCh16, AssertPropertyNonOverlappingImplication) {
  auto result = EvalImplication(true, false, true);
  EXPECT_EQ(result, PropertyResult::kPending);

  EXPECT_EQ(ResolveNonOverlapping(true), PropertyResult::kPass);

  EXPECT_EQ(ResolveNonOverlapping(false), PropertyResult::kFail);
}

TEST(SimCh16, AssertPropertyVacuousPassAntecedentFalse) {
  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, true), PropertyResult::kVacuousPass);
}

TEST(SimCh16, AssertPropertyDisableIffConditionTrue) {
  EXPECT_EQ(EvalWithDisableIff(true, PropertyResult::kFail),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalWithDisableIff(true, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
}

TEST(SimCh16, AssertPropertyDisableIffConditionFalse) {
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalWithDisableIff(false, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

TEST(SimCh16, AssertPropertySequenceDelay) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 3;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  std::vector<uint64_t> vals_pass = {1, 0, 0, 1};
  EXPECT_TRUE(MatchDelaySequence(seq, vals_pass));

  std::vector<uint64_t> vals_fail = {1, 0, 0, 0};
  EXPECT_FALSE(MatchDelaySequence(seq, vals_fail));
}

TEST(SimCh16, AssertPropertyConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 4;
  seq.rep_max = 4;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1}));

  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1, 0}));

  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1}));
}

TEST(SimCh16, AssertPropertyGotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1, 0, 1}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0, 1, 0}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 1}));
}

TEST(SimCh16, AssertPropertyNonConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 1, 0}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 1, 1}));

  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 0}));
}

TEST(SimCh16, PropertyNotOperator) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);

  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

TEST(SimCh16, PropertyAndOperator) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);

  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(SimCh16, PropertyOrOperator) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);

  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(SimCh16, SequenceAndOperator) {
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceAnd(true, false));
  EXPECT_FALSE(EvalSequenceAnd(false, true));
  EXPECT_FALSE(EvalSequenceAnd(false, false));
}

TEST(SimCh16, SequenceOrOperator) {
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

TEST(SimCh16, SequenceIntersectOperator) {
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 5, 5));

  EXPECT_FALSE(EvalSequenceIntersect(true, true, 5, 6));

  EXPECT_FALSE(EvalSequenceIntersect(true, false, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, true, 5, 5));
}

TEST(SimCh16, SequenceThroughoutOperator) {
  auto check = [](uint64_t v) { return v != 0; };
  EXPECT_TRUE(EvalThroughout(check, {1, 2, 3, 4}));

  EXPECT_FALSE(EvalThroughout(check, {1, 0, 3, 4}));

  EXPECT_TRUE(EvalThroughout(check, {}));
}
