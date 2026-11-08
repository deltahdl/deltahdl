#include "elaborator/covergroup_in_checker.h"

namespace delta {

bool CheckerCovergroupPlacementIsLegal(CheckerCovergroupPlacement placement) {
  return placement == CheckerCovergroupPlacement::kCheckerBody;
}

bool CheckerCovergroupMayReference(CheckerCovergroupReference reference) {
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
  return formal_referenced_by_covergroup && actual_is_const;
}

bool CheckerCovergroupTriggerIsPermitted(CheckerCovergroupTrigger trigger) {
  switch (trigger) {
    case CheckerCovergroupTrigger::kClockingEvent:
    case CheckerCovergroupTrigger::kProceduralSampleCall:
      return true;
  }
  return false;
}

}  // namespace delta
