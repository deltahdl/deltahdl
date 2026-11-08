#include "simulator/checker_variable_randomization.h"

#include <cstdint>

#include "common/types.h"
#include "simulator/checker_instance_scheduling.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

bool CheckerAssumeStatementIsCheckedForViolationDuringSimulation() {
  return true;
}

bool AssumeRandomizationIsTriggeredBy(RandomizationTrigger trigger) {
  return trigger == RandomizationTrigger::kAssumeSetClockEvent;
}

bool CheckersProvideRandomizeMethod() { return false; }

AssumeRandomizationHoldBoundary FreeCheckerVariableHoldEndsAt(
    bool next_clock_event_before_end_of_time_step) {
  return next_clock_event_before_end_of_time_step
             ? AssumeRandomizationHoldBoundary::kNextAssumeSetClockEvent
             : AssumeRandomizationHoldBoundary::kEndOfTimeStep;
}

bool IsActiveForAssumeRandomization(AssumeRandomizationVariable var) {
  switch (var) {
    case AssumeRandomizationVariable::kFreeNonConstUnassigned:
      return true;
    case AssumeRandomizationVariable::kFreeNonConstAssigned:
    case AssumeRandomizationVariable::kNonFreeCheckerVariable:
    case AssumeRandomizationVariable::kCheckerFormal:
      return false;
  }
  return false;
}

bool AssumeRandomizationProvidesActivenessControlFacility() { return false; }

bool AssumeRandomizationElementsAreSeparatelyActive(
    CheckerVariableAggregate agg) {
  return agg == CheckerVariableAggregate::kUnpackedArrayOrStruct;
}

bool FreeCheckerVariableTakesRandomInitialValue(
    bool has_declaration_initializer) {
  return !has_declaration_initializer;
}

int AssumeSetsPerCheckerInstance() { return 1; }

bool AssumeSetMayBeEmpty() { return true; }

bool AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind kind) {
  switch (kind) {
    case CheckerInstanceKind::kStatic:
    case CheckerInstanceKind::kProcedural:
      return true;
  }
  return true;
}

bool AssumeStatementOriginContributesToAssumeSet(AssumeStatementOrigin origin) {
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
  if (statement.references_const_cast_or_automatic_actual) {
    return false;
  }
  return statement.references_active_free_variable;
}

SolutionAttemptOutcome AssumeSetSolutionAttempt(bool satisfying_values_found) {
  return satisfying_values_found ? SolutionAttemptOutcome::kSuccessful
                                 : SolutionAttemptOutcome::kUnsuccessful;
}

bool AssumeRandomizationMustFindSolutionWhenItExists() { return false; }

bool AssumeRandomizationMustAvoidDeadEndStates() { return false; }

bool EmptyAssumeSetHasImplicitClockEvent() { return true; }

Region EmptyAssumeSetImplicitClockEventRegion() { return Region::kPreObserved; }

AssumeSetClocking ActiveVariableClocking(bool assume_set_is_empty) {
  return assume_set_is_empty ? AssumeSetClocking::kImplicitlyClocked
                             : AssumeSetClocking::kExplicitlyClocked;
}

bool ImplicitlyClockedVariableUpdatesEveryTimeStep() { return true; }

bool ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep() { return true; }

AssumeSetClocking ActiveVariableAbsentFromNonemptyAssumeSetClocking() {
  return AssumeSetClocking::kExplicitlyClocked;
}

bool ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained() { return false; }

Region AssumeRandomizationSolvePrecedesRegion() { return Region::kObserved; }

bool SampledValueOfActiveCheckerVariableIsCurrentValue() {
  constexpr uint64_t kProbeCurrentValue = 0xA5A5A5A5ULL;
  SampledValue sampled = SampleActiveFreeCheckerVariable(kProbeCurrentValue);
  return sampled.mode == SampleMode::kCurrent &&
         sampled.value == kProbeCurrentValue;
}

Region AssumptionFailureRegionAfterUnsuccessfulSolve() {
  return Region::kObserved;
}

}  // namespace delta
