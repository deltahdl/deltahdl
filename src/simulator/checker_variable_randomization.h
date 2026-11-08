#ifndef DELTA_SIMULATOR_CHECKER_VARIABLE_RANDOMIZATION_H
#define DELTA_SIMULATOR_CHECKER_VARIABLE_RANDOMIZATION_H

#include <cstdint>

#include "common/types.h"
#include "simulator/checker_instance_scheduling.h"

namespace delta {

bool CheckerAssumeStatementIsCheckedForViolationDuringSimulation();

enum class RandomizationTrigger : uint8_t {
  kAssumeSetClockEvent,
  kExplicitProceduralCall,
};

bool AssumeRandomizationIsTriggeredBy(RandomizationTrigger trigger);

bool CheckersProvideRandomizeMethod();

enum class AssumeRandomizationHoldBoundary : uint8_t {
  kNextAssumeSetClockEvent,
  kEndOfTimeStep,
};

AssumeRandomizationHoldBoundary FreeCheckerVariableHoldEndsAt(
    bool next_clock_event_before_end_of_time_step);

enum class AssumeRandomizationVariable : uint8_t {
  kFreeNonConstUnassigned,
  kFreeNonConstAssigned,
  kNonFreeCheckerVariable,
  kCheckerFormal,
};

bool IsActiveForAssumeRandomization(AssumeRandomizationVariable var);

bool AssumeRandomizationProvidesActivenessControlFacility();

enum class CheckerVariableAggregate : uint8_t {
  kPackedArrayOrStruct,
  kUnpackedArrayOrStruct,
};

bool AssumeRandomizationElementsAreSeparatelyActive(
    CheckerVariableAggregate agg);

bool FreeCheckerVariableTakesRandomInitialValue(
    bool has_declaration_initializer);

int AssumeSetsPerCheckerInstance();

bool AssumeSetMayBeEmpty();

bool AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind kind);

enum class AssumeStatementOrigin : uint8_t {
  kOwnChecker,
  kChildChecker,
  kUnrelated,
};

bool AssumeStatementOriginContributesToAssumeSet(AssumeStatementOrigin origin);

struct AssumeStatementMembership {
  bool references_const_cast_or_automatic_actual;
  bool references_active_free_variable;
};

bool AssumeStatementIsInAssumeSet(const AssumeStatementMembership& statement);

enum class SolutionAttemptOutcome : uint8_t {
  kSuccessful,
  kUnsuccessful,
};

SolutionAttemptOutcome AssumeSetSolutionAttempt(bool satisfying_values_found);

bool AssumeRandomizationMustFindSolutionWhenItExists();

bool AssumeRandomizationMustAvoidDeadEndStates();

bool EmptyAssumeSetHasImplicitClockEvent();

Region EmptyAssumeSetImplicitClockEventRegion();

enum class AssumeSetClocking : uint8_t {
  kImplicitlyClocked,
  kExplicitlyClocked,
};

AssumeSetClocking ActiveVariableClocking(bool assume_set_is_empty);

bool ImplicitlyClockedVariableUpdatesEveryTimeStep();

bool ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep();

AssumeSetClocking ActiveVariableAbsentFromNonemptyAssumeSetClocking();

bool ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained();

Region AssumeRandomizationSolvePrecedesRegion();

bool SampledValueOfActiveCheckerVariableIsCurrentValue();

Region AssumptionFailureRegionAfterUnsuccessfulSolve();

}  // namespace delta

#endif
