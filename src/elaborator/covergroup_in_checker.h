#ifndef DELTA_ELABORATOR_COVERGROUP_IN_CHECKER_H
#define DELTA_ELABORATOR_COVERGROUP_IN_CHECKER_H

#include <cstdint>

namespace delta {

enum class CheckerCovergroupPlacement : uint8_t {
  kCheckerBody,
  kProceduralBlock,
};

bool CheckerCovergroupPlacementIsLegal(CheckerCovergroupPlacement placement);

enum class CheckerCovergroupReference : uint8_t {
  kCheckerFormalArgument,
  kCheckerVariable,
  kOtherVisibleVariable,
};

bool CheckerCovergroupMayReference(CheckerCovergroupReference reference);

bool CheckerCovergroupConstFormalIsError(bool formal_referenced_by_covergroup,
                                         bool actual_is_const);

enum class CheckerCovergroupTrigger : uint8_t {
  kClockingEvent,
  kProceduralSampleCall,
};

bool CheckerCovergroupTriggerIsPermitted(CheckerCovergroupTrigger trigger);

}  // namespace delta

#endif
