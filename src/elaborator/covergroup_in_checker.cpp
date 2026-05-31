#include "elaborator/covergroup_in_checker.h"

namespace delta {

bool CheckerCovergroupPlacementIsLegal(CheckerCovergroupPlacement placement) {
  // §17.6: covergroup declarations and instances are permitted in the checker
  // body but shall not appear in any procedural block of the checker.
  return placement == CheckerCovergroupPlacement::kCheckerBody;
}

bool CheckerCovergroupMayReference(CheckerCovergroupReference reference) {
  // §17.6: a covergroup may reference any variable visible in its scope. Within
  // a checker that set includes the checker's formal arguments and its checker
  // variables, so every visible reference kind is allowed.
  switch (reference) {
    case CheckerCovergroupReference::kCheckerFormalArgument:
    case CheckerCovergroupReference::kCheckerVariable:
    case CheckerCovergroupReference::kOtherVisibleVariable:
      return true;
  }
  return false;
}

bool CheckerCovergroupConstFormalIsError(bool formal_referenced_by_covergroup,
                                         bool actual_is_const) {
  // §17.6: it shall be an error if a formal argument referenced by a covergroup
  // has a const actual argument. Both conditions must hold for the error.
  return formal_referenced_by_covergroup && actual_is_const;
}

bool CheckerCovergroupTriggerIsPermitted(CheckerCovergroupTrigger trigger) {
  // §17.6: a covergroup in a checker may be triggered by its clocking event and
  // may also be triggered by a procedural call to its sample() method.
  switch (trigger) {
    case CheckerCovergroupTrigger::kClockingEvent:
    case CheckerCovergroupTrigger::kProceduralSampleCall:
      return true;
  }
  return false;
}

}  // namespace delta
