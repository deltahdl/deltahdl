#include "elaborator/checker_variable_assignment.h"

namespace delta {

bool CheckerVariableAssignmentFormIsAvailable(CheckerVariableAssignment form) {
  switch (form) {
    case CheckerVariableAssignment::kBlockingProcedural:
    case CheckerVariableAssignment::kNonblockingProcedural:
    case CheckerVariableAssignment::kContinuous:
      return true;
  }
  return false;
}

bool AlwaysFfAdmitsCheckerVariableAssignment(CheckerVariableAssignment form) {
  switch (form) {
    case CheckerVariableAssignment::kNonblockingProcedural:
      return true;
    case CheckerVariableAssignment::kBlockingProcedural:
    case CheckerVariableAssignment::kContinuous:
      return false;
  }
  return false;
}

bool CheckerVariableAssignmentReferenceIsLegal(CheckerVariableReference ref) {
  switch (ref) {
    case CheckerVariableReference::kSimpleName:
      return true;
    case CheckerVariableReference::kHierarchicalName:
      return false;
  }
  return false;
}

bool FreeCheckerVariableAssignmentIsLegal(CheckerVariableAssignment form) {
  switch (form) {
    case CheckerVariableAssignment::kNonblockingProcedural:
      return true;
    case CheckerVariableAssignment::kContinuous:
    case CheckerVariableAssignment::kBlockingProcedural:
      return false;
  }
  return false;
}

bool CheckerVariableAssignmentSiteIsLegal(CheckerVariableAssignmentSite site) {
  switch (site) {
    case CheckerVariableAssignmentSite::kDeclarationInitializer:
      return true;
    case CheckerVariableAssignmentSite::kInitialProcedure:
      return false;
  }
  return false;
}

bool CheckerVariableAssignmentRhsMayContainTriggered() { return true; }

bool NonblockingAssignmentLhsMayBeFreeCheckerVariable() { return true; }

}  // namespace delta
