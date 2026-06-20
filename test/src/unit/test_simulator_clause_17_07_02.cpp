#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/checker_variable_randomization.h"

using namespace delta;

namespace {

// §17.7.2: like ordinary assume statements, a checker assume statement is also
// checked for violation during simulation.
TEST(CheckerVariableRandomization, CheckerAssumeIsCheckedForViolation) {
  EXPECT_TRUE(CheckerAssumeStatementIsCheckedForViolationDuringSimulation());
}

// §17.7.2: solving is triggered by an assume set clock event, not by an
// explicit procedural call such as randomize().
TEST(CheckerVariableRandomization, SolveTriggeredByAssumeSetClockEvent) {
  EXPECT_TRUE(AssumeRandomizationIsTriggeredBy(
      RandomizationTrigger::kAssumeSetClockEvent));
  EXPECT_FALSE(AssumeRandomizationIsTriggeredBy(
      RandomizationTrigger::kExplicitProceduralCall));
}

// §17.7.2: there is no randomize() for checkers.
TEST(CheckerVariableRandomization, CheckersHaveNoRandomizeMethod) {
  EXPECT_FALSE(CheckersProvideRandomizeMethod());
}

// §17.7.2: an updated free checker variable holds its value until the next
// assume set clock event or the end of the time step, whichever comes first.
TEST(CheckerVariableRandomization, HoldEndsAtWhicheverComesFirst) {
  EXPECT_EQ(FreeCheckerVariableHoldEndsAt(
                /*next_clock_event_before_end_of_time_step=*/true),
            AssumeRandomizationHoldBoundary::kNextAssumeSetClockEvent);
  EXPECT_EQ(FreeCheckerVariableHoldEndsAt(
                /*next_clock_event_before_end_of_time_step=*/false),
            AssumeRandomizationHoldBoundary::kEndOfTimeStep);
}

// §17.7.2: a non-const free checker variable is active unless it appears on the
// left-hand side of a checker variable assignment, in which case it is
// inactive; non-free checker variables and checker formals are always inactive.
TEST(CheckerVariableRandomization, ActiveClassification) {
  EXPECT_TRUE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kFreeNonConstUnassigned));
  EXPECT_FALSE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kFreeNonConstAssigned));
  EXPECT_FALSE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kNonFreeCheckerVariable));
  EXPECT_FALSE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kCheckerFormal));
}

// §17.7.2: activeness mirrors rand variables but without an explicit control
// facility such as rand_mode().
TEST(CheckerVariableRandomization, NoActivenessControlFacility) {
  EXPECT_FALSE(AssumeRandomizationProvidesActivenessControlFacility());
}

// §17.7.2: a packed array or structure is active or inactive monolithically,
// whereas the elements of an unpacked array or structure are separately active.
TEST(CheckerVariableRandomization, ElementActivenessGranularity) {
  EXPECT_FALSE(AssumeRandomizationElementsAreSeparatelyActive(
      CheckerVariableAggregate::kPackedArrayOrStruct));
  EXPECT_TRUE(AssumeRandomizationElementsAreSeparatelyActive(
      CheckerVariableAggregate::kUnpackedArrayOrStruct));
}

// §17.7.2: every free checker variable is initialized with an unconstrained
// random value unless explicitly initialized in its declaration.
TEST(CheckerVariableRandomization, RandomInitialValueUnlessDeclared) {
  EXPECT_TRUE(FreeCheckerVariableTakesRandomInitialValue(
      /*has_declaration_initializer=*/false));
  EXPECT_FALSE(FreeCheckerVariableTakesRandomInitialValue(
      /*has_declaration_initializer=*/true));
}

// §17.7.2: each checker instance has one and only one assume set, which may be
// empty.
TEST(CheckerVariableRandomization, OneAssumeSetPerInstanceMaybeEmpty) {
  EXPECT_EQ(AssumeSetsPerCheckerInstance(), 1);
  EXPECT_TRUE(AssumeSetMayBeEmpty());
}

// §17.7.2: checker assume sets exist at every time step regardless of whether
// the checker instance is static or procedural.
TEST(CheckerVariableRandomization, AssumeSetExistsForStaticAndProcedural) {
  EXPECT_TRUE(AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind::kStatic));
  EXPECT_TRUE(AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind::kProcedural));
}

// §17.7.2: an assume set is formed from the checker's own assume statements and
// those of its child checkers; unrelated statements do not contribute.
TEST(CheckerVariableRandomization, AssumeSetOriginContribution) {
  EXPECT_TRUE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kOwnChecker));
  EXPECT_TRUE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kChildChecker));
  EXPECT_FALSE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kUnrelated));
}

// §17.7.2: a candidate statement that references a const-cast or
// automatic-value actual is excluded; of the rest, only those referencing an
// active free variable are included.
TEST(CheckerVariableRandomization, AssumeSetMembership) {
  // Excluded because of the const-cast / automatic actual, even though it would
  // otherwise reference an active free variable.
  EXPECT_FALSE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/true, /*active_free_var=*/true}));
  // Included: no excluded actual, and it references an active free variable.
  EXPECT_TRUE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/false, /*active_free_var=*/true}));
  // Not included: no excluded actual, but references no active free variable.
  EXPECT_FALSE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/false, /*active_free_var=*/false}));
}

// §17.7.2: a solution attempt is successful exactly when satisfying values are
// found for the active variables; otherwise it is unsuccessful.
TEST(CheckerVariableRandomization, SolutionAttemptOutcome) {
  EXPECT_EQ(AssumeSetSolutionAttempt(/*satisfying_values_found=*/true),
            SolutionAttemptOutcome::kSuccessful);
  EXPECT_EQ(AssumeSetSolutionAttempt(/*satisfying_values_found=*/false),
            SolutionAttemptOutcome::kUnsuccessful);
}

// §17.7.2: there is no requirement that a solution be found when one exists,
// nor that dead-end states be avoided.
TEST(CheckerVariableRandomization, NoSolutionGuarantees) {
  EXPECT_FALSE(AssumeRandomizationMustFindSolutionWhenItExists());
  EXPECT_FALSE(AssumeRandomizationMustAvoidDeadEndStates());
}

// §17.7.2: an empty assume set carries an implicit assume set clock event in
// every time step, placed before the Observed region.
TEST(CheckerVariableRandomization, EmptyAssumeSetImplicitClock) {
  EXPECT_TRUE(EmptyAssumeSetHasImplicitClockEvent());
  EXPECT_EQ(EmptyAssumeSetImplicitClockEventRegion(), Region::kPreObserved);
  // The implicit event precedes the Observed region in the region order.
  EXPECT_LT(static_cast<int>(EmptyAssumeSetImplicitClockEventRegion()),
            static_cast<int>(Region::kObserved));
}

// §17.7.2: active variables of a checker with an empty assume set are
// implicitly clocked; with a nonempty assume set they are explicitly clocked.
TEST(CheckerVariableRandomization, ActiveVariableClocking) {
  EXPECT_EQ(ActiveVariableClocking(/*assume_set_is_empty=*/true),
            AssumeSetClocking::kImplicitlyClocked);
  EXPECT_EQ(ActiveVariableClocking(/*assume_set_is_empty=*/false),
            AssumeSetClocking::kExplicitlyClocked);
}

// §17.7.2: an implicitly clocked active free variable may be updated at every
// time step and then stays constant until the end of the time step.
TEST(CheckerVariableRandomization, ImplicitlyClockedUpdateAndHold) {
  EXPECT_TRUE(ImplicitlyClockedVariableUpdatesEveryTimeStep());
  EXPECT_TRUE(ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep());
}

// §17.7.2: an active variable that appears in no property of a nonempty assume
// set is unconstrained but still explicitly clocked.
TEST(CheckerVariableRandomization,
     AbsentActiveVariableUnconstrainedButClocked) {
  EXPECT_EQ(ActiveVariableAbsentFromNonemptyAssumeSetClocking(),
            AssumeSetClocking::kExplicitlyClocked);
  EXPECT_FALSE(ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained());
}

// §17.7.2: the active free checker variables are solved for as the
// implementation is about to begin the Observed region, using sampled values
// that, for an active checker variable, are its current value.
TEST(CheckerVariableRandomization, SolveAtObservedWithCurrentValues) {
  EXPECT_EQ(AssumeRandomizationSolvePrecedesRegion(), Region::kObserved);
  EXPECT_TRUE(SampledValueOfActiveCheckerVariableIsCurrentValue());
}

// §17.7.2: after an unsuccessful solution attempt, an assumption failure does
// not occur until the unsatisfied property is clocked and checked in the
// Observed region.
TEST(CheckerVariableRandomization, UnsuccessfulFailureSurfacesInObserved) {
  EXPECT_EQ(AssumptionFailureRegionAfterUnsuccessfulSolve(), Region::kObserved);
}

}  // namespace
