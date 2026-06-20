#ifndef DELTA_ELABORATOR_COVERGROUP_IN_CHECKER_H
#define DELTA_ELABORATOR_COVERGROUP_IN_CHECKER_H

#include <cstdint>

namespace delta {

// §17.6 governs the use of covergroups inside a checker. A checker body may
// carry one or more covergroup declarations or instances, subject to two
// placement and reference rules and one legality error that are specific to the
// checker context. The covergroup construct itself (its declaration syntax and
// coverpoints) belongs to §19.3, and the sample() method that triggers a
// covergroup belongs to §19.8 (with its user-defined override in §19.8.1); the
// helpers here model only the rules the text of §17.6 adds on top of those: how
// a checker constrains where a covergroup may sit, what it may reference, when
// a referenced formal makes the construct illegal, and how it may be triggered.

// §17.6: where a covergroup declaration or instance appears relative to the
// checker body.
enum class CheckerCovergroupPlacement : uint8_t {
  // Written directly in the checker body (or a non-procedural nested scope).
  kCheckerBody,
  // Written inside a procedural block of the checker, such as an always or
  // initial block.
  kProceduralBlock,
};

// §17.6: a covergroup declaration or instance is permitted within a checker,
// but it shall not appear in any procedural block of that checker. A placement
// in the checker body is therefore legal, while a placement inside a procedural
// block is not.
bool CheckerCovergroupPlacementIsLegal(CheckerCovergroupPlacement placement);

// §17.6: the kinds of names a covergroup contained in a checker may read.
enum class CheckerCovergroupReference : uint8_t {
  // A formal argument of the enclosing checker.
  kCheckerFormalArgument,
  // A checker variable declared in the checker body.
  kCheckerVariable,
  // Any other variable that is visible in the covergroup's scope.
  kOtherVisibleVariable,
};

// §17.6: a covergroup may reference any variable visible in its scope; inside a
// checker that visible set expressly includes the checker's formal arguments
// and its checker variables. Every such reference kind is therefore allowed.
bool CheckerCovergroupMayReference(CheckerCovergroupReference reference);

// §17.6: it shall be an error if a formal argument that a covergroup references
// is bound, at the instantiation, to a const actual argument. The combination
// is an error only when both conditions hold — the formal is actually
// referenced by a covergroup and its actual is const.
bool CheckerCovergroupConstFormalIsError(bool formal_referenced_by_covergroup,
                                         bool actual_is_const);

// §17.6: the ways a covergroup inside a checker can be triggered to sample.
enum class CheckerCovergroupTrigger : uint8_t {
  // The covergroup's own clocking event.
  kClockingEvent,
  // A procedural call to the covergroup's sample() method (see §19.8).
  kProceduralSampleCall,
};

// §17.6: besides being triggered by its clocking event, a covergroup in a
// checker may also be triggered by a procedural call to its sample() method.
// Both trigger forms are permitted.
bool CheckerCovergroupTriggerIsPermitted(CheckerCovergroupTrigger trigger);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_IN_CHECKER_H
