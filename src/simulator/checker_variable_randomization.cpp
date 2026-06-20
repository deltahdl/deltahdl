#include "simulator/checker_variable_randomization.h"

namespace delta {

bool CheckerAssumeStatementIsCheckedForViolationDuringSimulation() {
  // §17.7.2: checker assume statements behave like ordinary assume statements
  // in that they are also checked for violation during simulation.
  return true;
}

bool AssumeRandomizationIsTriggeredBy(RandomizationTrigger trigger) {
  // §17.7.2: solving is triggered by any of the clock events of the properties
  // in the assume set, not by an explicit procedural call.
  return trigger == RandomizationTrigger::kAssumeSetClockEvent;
}

bool CheckersProvideRandomizeMethod() {
  // §17.7.2: there is no randomize() for checkers.
  return false;
}

AssumeRandomizationHoldBoundary FreeCheckerVariableHoldEndsAt(
    bool next_clock_event_before_end_of_time_step) {
  // §17.7.2: an updated free checker variable holds its value until the next
  // assume set clock event or the end of the time step, whichever comes first.
  return next_clock_event_before_end_of_time_step
             ? AssumeRandomizationHoldBoundary::kNextAssumeSetClockEvent
             : AssumeRandomizationHoldBoundary::kEndOfTimeStep;
}

bool IsActiveForAssumeRandomization(AssumeRandomizationVariable var) {
  switch (var) {
    case AssumeRandomizationVariable::kFreeNonConstUnassigned:
      // §17.7.2: a non-const free checker variable that is not assigned is
      // active.
      return true;
    case AssumeRandomizationVariable::kFreeNonConstAssigned:
      // §17.7.2: a free checker variable appearing on the left-hand side of a
      // checker variable assignment is inactive.
      return false;
    case AssumeRandomizationVariable::kNonFreeCheckerVariable:
    case AssumeRandomizationVariable::kCheckerFormal:
      // §17.7.2: all other variables — non-free checker variables and checker
      // formals — are always treated as inactive.
      return false;
  }
  return false;
}

bool AssumeRandomizationProvidesActivenessControlFacility() {
  // §17.7.2: activeness mirrors rand variables but carries no explicit control
  // facility such as rand_mode().
  return false;
}

bool AssumeRandomizationElementsAreSeparatelyActive(
    CheckerVariableAggregate agg) {
  // §17.7.2: a packed array or structure is active or inactive monolithically,
  // whereas the elements of an unpacked array or structure are separately
  // active or inactive.
  return agg == CheckerVariableAggregate::kUnpackedArrayOrStruct;
}

bool FreeCheckerVariableTakesRandomInitialValue(
    bool has_declaration_initializer) {
  // §17.7.2: every free checker variable is initialized with an unconstrained
  // random value unless explicitly initialized in its declaration.
  return !has_declaration_initializer;
}

int AssumeSetsPerCheckerInstance() {
  // §17.7.2: each checker instance has one and only one assume set.
  return 1;
}

bool AssumeSetMayBeEmpty() {
  // §17.7.2: that single assume set may be empty.
  return true;
}

bool AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind kind) {
  // §17.7.2: checker assume sets are considered to exist at every time step,
  // regardless of whether the checker instance is static or procedural.
  switch (kind) {
    case CheckerInstanceKind::kStatic:
    case CheckerInstanceKind::kProcedural:
      return true;
  }
  return true;
}

bool AssumeStatementOriginContributesToAssumeSet(AssumeStatementOrigin origin) {
  // §17.7.2: the assume set is formed from the checker's own assume statements
  // and those of its child checkers.
  switch (origin) {
    case AssumeStatementOrigin::kOwnChecker:
    case AssumeStatementOrigin::kChildChecker:
      return true;
    case AssumeStatementOrigin::kUnrelated:
      return false;
  }
  return false;
}

bool AssumeStatementIsInAssumeSet(const AssumeStatementMembership& statement) {
  // §17.7.2: a statement referencing a formal whose actual argument contains a
  // const cast or automatic-value subexpression is excluded from the assume
  // set.
  if (statement.references_const_cast_or_automatic_actual) {
    return false;
  }
  // §17.7.2: among the remaining statements, only those referencing an active
  // free variable of the checker are included.
  return statement.references_active_free_variable;
}

SolutionAttemptOutcome AssumeSetSolutionAttempt(bool satisfying_values_found) {
  // §17.7.2: the attempt is successful when values are found for all active
  // checker variables that keep every assumption from failing in the time step;
  // otherwise the attempt is unsuccessful.
  return satisfying_values_found ? SolutionAttemptOutcome::kSuccessful
                                 : SolutionAttemptOutcome::kUnsuccessful;
}

bool AssumeRandomizationMustFindSolutionWhenItExists() {
  // §17.7.2: there is no requirement that a solution be found even if it
  // exists.
  return false;
}

bool AssumeRandomizationMustAvoidDeadEndStates() {
  // §17.7.2: there is no requirement that dead-end states be avoided.
  return false;
}

bool EmptyAssumeSetHasImplicitClockEvent() {
  // §17.7.2: an empty assume set is considered to have an implicit assume set
  // clock event in every time step.
  return true;
}

Region EmptyAssumeSetImplicitClockEventRegion() {
  // §17.7.2: that implicit clock event is placed before the Observed region.
  return Region::kPreObserved;
}

AssumeSetClocking ActiveVariableClocking(bool assume_set_is_empty) {
  // §17.7.2: active variables of a checker with an empty assume set are
  // implicitly clocked; with a nonempty assume set they are explicitly clocked.
  return assume_set_is_empty ? AssumeSetClocking::kImplicitlyClocked
                             : AssumeSetClocking::kExplicitlyClocked;
}

bool ImplicitlyClockedVariableUpdatesEveryTimeStep() {
  // §17.7.2: implicitly clocked active free variables may be updated with
  // unconstrained random values at every time step.
  return true;
}

bool ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep() {
  // §17.7.2: once updated, an implicitly clocked active free variable stays
  // constant until the end of the time step.
  return true;
}

AssumeSetClocking ActiveVariableAbsentFromNonemptyAssumeSetClocking() {
  // §17.7.2: an active variable that appears in no property of a nonempty
  // assume set is still explicitly clocked.
  return AssumeSetClocking::kExplicitlyClocked;
}

bool ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained() {
  // §17.7.2: such an active variable is unconstrained.
  return false;
}

Region AssumeRandomizationSolvePrecedesRegion() {
  // §17.7.2: the active free checker variables are solved for as the
  // implementation is about to begin the Observed region.
  return Region::kObserved;
}

bool SampledValueOfActiveCheckerVariableIsCurrentValue() {
  // §17.7.2: the sampled value of an active checker variable is its current
  // value (see §16.5.1).
  return true;
}

Region AssumptionFailureRegionAfterUnsuccessfulSolve() {
  // §17.7.2: after an unsuccessful solution attempt, an assumption failure does
  // not occur until the unsatisfied property is clocked and checked in the
  // Observed region.
  return Region::kObserved;
}

}  // namespace delta
