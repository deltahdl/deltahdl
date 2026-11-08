#ifndef DELTA_ELABORATOR_CHECKER_VARIABLE_ASSIGNMENT_H
#define DELTA_ELABORATOR_CHECKER_VARIABLE_ASSIGNMENT_H

#include <cstdint>

namespace delta {

enum class CheckerVariableAssignment : uint8_t {
  kBlockingProcedural,
  kNonblockingProcedural,
  kContinuous,
};

bool CheckerVariableAssignmentFormIsAvailable(CheckerVariableAssignment form);

bool AlwaysFfAdmitsCheckerVariableAssignment(CheckerVariableAssignment form);

enum class CheckerVariableReference : uint8_t {
  kSimpleName,
  kHierarchicalName,
};

bool CheckerVariableAssignmentReferenceIsLegal(CheckerVariableReference ref);

bool FreeCheckerVariableAssignmentIsLegal(CheckerVariableAssignment form);

enum class CheckerVariableAssignmentSite : uint8_t {
  kInitialProcedure,
  kDeclarationInitializer,
};

bool CheckerVariableAssignmentSiteIsLegal(CheckerVariableAssignmentSite site);

bool CheckerVariableAssignmentRhsMayContainTriggered();

bool NonblockingAssignmentLhsMayBeFreeCheckerVariable();

}  // namespace delta

#endif
