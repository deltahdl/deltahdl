#ifndef DELTA_SIMULATOR_CHECKER_VARIABLE_RANDOMIZATION_H
#define DELTA_SIMULATOR_CHECKER_VARIABLE_RANDOMIZATION_H

#include <cstdint>

#include "common/types.h"

namespace delta {

// §17.7.2 describes assume-based checker variable randomization: how a
// simulator periodically solves the assume statements of a checker instance to
// find values for its free checker variables and then updates them. The helpers
// here model only the rules the text of §17.7.2 states directly — which
// variables are active, how the assume set is formed, what a solution attempt
// does, when free variables are randomized and how long they hold, and where in
// the region order the solve and any resulting failures occur. Each rule is
// encoded as a pure function so it can be observed in isolation. The
// active/inactive analogy to rand variables is owned by §17.9, the
// sampled-value definition by §16.5.1, the region order by §4 scheduling, and
// the checker-instance lifetime by §17.3; this file only records how §17.7.2
// scopes those onto checker randomization.

// §17.7.2: like ordinary assume statements, a checker assume statement is also
// checked for violation during simulation.
bool CheckerAssumeStatementIsCheckedForViolationDuringSimulation();

// §17.7.2: what triggers an assume-based randomization solve.
enum class RandomizationTrigger : uint8_t {
  kAssumeSetClockEvent,     // a clock event of a property in the assume set
  kExplicitProceduralCall,  // an explicit call such as randomize()
};

// §17.7.2: solving is triggered by an assume set clock event, not by an
// explicit procedural call. Returns true only for the assume set clock event
// trigger.
bool AssumeRandomizationIsTriggeredBy(RandomizationTrigger trigger);

// §17.7.2: there is no randomize() for checkers, so checkers expose no
// procedural randomization method.
bool CheckersProvideRandomizeMethod();

// §17.7.2: the boundary at which a free checker variable stops holding its
// updated value.
enum class AssumeRandomizationHoldBoundary : uint8_t {
  kNextAssumeSetClockEvent,  // the next assume set clock event
  kEndOfTimeStep,            // the end of the current time step
};

// §17.7.2: once updated with solution values, a free checker variable remains
// constant until the next assume set clock event or the end of the time step,
// whichever comes first. Given whether the next assume set clock event precedes
// the end of the time step, returns the boundary that ends the hold.
AssumeRandomizationHoldBoundary FreeCheckerVariableHoldEndsAt(
    bool next_clock_event_before_end_of_time_step);

// §17.7.2: the categories of variable that assume-based randomization
// distinguishes when deciding which variables it may solve for.
enum class AssumeRandomizationVariable : uint8_t {
  // A non-const free checker variable that does not appear on the left-hand
  // side
  // of a checker variable assignment.
  kFreeNonConstUnassigned,
  // A non-const free checker variable that appears on the left-hand side of a
  // checker variable assignment (see §17.7.1).
  kFreeNonConstAssigned,
  // An ordinary, non-free checker variable.
  kNonFreeCheckerVariable,
  // A checker formal argument.
  kCheckerFormal,
};

// §17.7.2: a non-const free checker variable is active unless it appears on the
// left-hand side of a checker variable assignment, in which case it is
// inactive; every other variable — a non-free checker variable or a checker
// formal — is always inactive. Returns true when the variable is treated as
// active.
bool IsActiveForAssumeRandomization(AssumeRandomizationVariable var);

// §17.7.2: activeness is treated in the same way as rand variables for
// class-based constrained random generation, but without an explicit control
// facility such as rand_mode(). Returns false: there is no such facility.
bool AssumeRandomizationProvidesActivenessControlFacility();

// §17.7.2: aggregate shapes whose elements may carry activeness independently.
enum class CheckerVariableAggregate : uint8_t {
  kPackedArrayOrStruct,    // active or inactive monolithically
  kUnpackedArrayOrStruct,  // elements separately active or inactive
};

// §17.7.2: activeness is decided for each singular element. A packed array or
// structure is active or inactive monolithically, whereas the elements of an
// unpacked array or structure are separately active or inactive. Returns true
// when the aggregate's elements carry independent activeness.
bool AssumeRandomizationElementsAreSeparatelyActive(
    CheckerVariableAggregate agg);

// §17.7.2: every free checker variable — const or non-const, active or inactive
// — is initialized with an unconstrained random value, unless its declaration
// supplies an explicit initializer. Returns true when randomization supplies
// the initial value, i.e., when the declaration has no initializer.
bool FreeCheckerVariableTakesRandomInitialValue(
    bool has_declaration_initializer);

// §17.7.2: a checker instance has one and only one assume set. Returns that
// count.
int AssumeSetsPerCheckerInstance();

// §17.7.2: a checker instance's assume set may be empty.
bool AssumeSetMayBeEmpty();

// §17.7.2: a checker instance may be static or procedural (see §17.3).
enum class CheckerInstanceKind : uint8_t {
  kStatic,
  kProcedural,
};

// §17.7.2: checker assume sets are considered to exist at every time step,
// regardless of whether the checker instance is static or procedural. Returns
// true for either kind.
bool AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind kind);

// §17.7.2: the provenance of an assume statement considered for an assume set.
enum class AssumeStatementOrigin : uint8_t {
  kOwnChecker,    // an assume statement of this checker
  kChildChecker,  // an assume statement of a child checker
  kUnrelated,     // an assume statement belonging to neither
};

// §17.7.2: an assume set is formed from the checker's own assume statements and
// the assume statements of its child checkers. Returns true when an assume
// statement of the given origin contributes to the assume set.
bool AssumeStatementOriginContributesToAssumeSet(AssumeStatementOrigin origin);

// §17.7.2: the attributes of a candidate assume statement that decide its
// membership in the assume set.
struct AssumeStatementMembership {
  // The statement references a formal whose actual argument contains a
  // subexpression that is a const cast or an automatic value (see §17.3).
  bool references_const_cast_or_automatic_actual;
  // The statement references an active free variable of the checker.
  bool references_active_free_variable;
};

// §17.7.2: a candidate assume statement that references a formal whose actual
// argument contains a const cast or automatic-value subexpression is excluded
// from the assume set; among the remaining statements, only those referencing
// an active free checker variable are included. Returns true when the statement
// is a member of the assume set.
bool AssumeStatementIsInAssumeSet(const AssumeStatementMembership& statement);

// §17.7.2: the outcome of one solution attempt on an assume set.
enum class SolutionAttemptOutcome : uint8_t {
  kSuccessful,
  kUnsuccessful,
};

// §17.7.2: a solution attempt seeks values for all active checker variables
// such that, together with the inactive variables and state, none of the
// assumptions fail in that time step. The attempt is successful exactly when
// such a set of values is found; otherwise any values may be chosen for the
// active variables and the attempt is unsuccessful.
SolutionAttemptOutcome AssumeSetSolutionAttempt(bool satisfying_values_found);

// §17.7.2: there is no requirement that a solution be found when one exists.
bool AssumeRandomizationMustFindSolutionWhenItExists();

// §17.7.2: there is no requirement that dead-end states (states from which no
// solution exists) be avoided.
bool AssumeRandomizationMustAvoidDeadEndStates();

// §17.7.2: an empty assume set is considered to carry an implicit assume set
// clock event in every time step. Returns true: the implicit event always
// exists for an empty assume set.
bool EmptyAssumeSetHasImplicitClockEvent();

// §17.7.2: that implicit assume set clock event of an empty assume set is
// placed before the Observed region. Returns the region in which it occurs.
Region EmptyAssumeSetImplicitClockEventRegion();

// §17.7.2: how the active free variables of a checker instance are clocked.
enum class AssumeSetClocking : uint8_t {
  kImplicitlyClocked,  // active variables of a checker with an empty assume set
  kExplicitlyClocked,  // active variables of a checker with a nonempty assume
                       // set
};

// §17.7.2: active variables in a checker with an empty assume set are
// implicitly clocked; those in a checker with a nonempty assume set are
// explicitly clocked.
AssumeSetClocking ActiveVariableClocking(bool assume_set_is_empty);

// §17.7.2: an implicitly clocked active free variable may be updated with an
// unconstrained random value at every time step. Returns true.
bool ImplicitlyClockedVariableUpdatesEveryTimeStep();

// §17.7.2: once an implicitly clocked active free variable is updated, it stays
// constant until the end of the time step. Returns true.
bool ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep();

// §17.7.2: an active variable that does not appear in any property of a
// nonempty assume set is unconstrained, yet still explicitly clocked. Returns
// its clocking.
AssumeSetClocking ActiveVariableAbsentFromNonemptyAssumeSetClocking();

// §17.7.2: such an active variable is unconstrained. Returns false: it carries
// no constraint.
bool ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained();

// §17.7.2: when an implementation is about to begin the Observed region it
// shall solve for all the active free checker variables. Returns the region
// whose beginning triggers that solve.
Region AssumeRandomizationSolvePrecedesRegion();

// §17.7.2: the solve uses sampled values of all other variables, and the
// sampled value of an active checker variable is its current value (see
// §16.5.1), rather than a preponed value. Returns true: the sampled value is
// the current value.
bool SampledValueOfActiveCheckerVariableIsCurrentValue();

// §17.7.2: when a solution attempt is unsuccessful, any resulting assumption
// failures do not occur until an unsatisfied property is clocked and checked in
// the Observed region. Returns the region in which such a failure surfaces.
Region AssumptionFailureRegionAfterUnsuccessfulSolve();

}  // namespace delta

#endif  // DELTA_SIMULATOR_CHECKER_VARIABLE_RANDOMIZATION_H
