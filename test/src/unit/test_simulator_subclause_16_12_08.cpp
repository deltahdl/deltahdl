#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, PropertyNot) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

// §16.12.8: `property_expr1 implies property_expr2` holds if, and only if, the
// antecedent fails to hold or the consequent holds. The antecedent holding with
// a holding consequent passes; a holding antecedent with a failing consequent
// fails; a failing antecedent holds vacuously regardless of the consequent.
TEST(SvaEngine, PropertyImplies) {
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.8: `property_expr1 iff property_expr2` holds if, and only if, the two
// operands' verdicts agree — both hold or both fail to hold; disagreement
// fails in either direction.
TEST(SvaEngine, PropertyIff) {
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.8: a vacuous pass counts as the operand holding, so it behaves like an
// ordinary pass on either side of implies and iff. The implies consequent is a
// distinct, asymmetric operand: a consequent that holds vacuously (as an inner
// vacuously passing property_expr does) still makes the implication hold, both
// when the antecedent holds and when it fails to hold.
TEST(SvaEngine, ImpliesIffTreatVacuousPassAsHolding) {
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kVacuousPass, PropertyResult::kPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
}

}  // namespace
