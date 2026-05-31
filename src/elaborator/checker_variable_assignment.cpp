#include "elaborator/checker_variable_assignment.h"

namespace delta {

bool CheckerVariableAssignmentFormIsAvailable(CheckerVariableAssignment form) {
  switch (form) {
    case CheckerVariableAssignment::kBlockingProcedural:
    case CheckerVariableAssignment::kNonblockingProcedural:
    case CheckerVariableAssignment::kContinuous:
      // §17.7.1: checker variables may be assigned using blocking and
      // nonblocking procedural assignments, or non-procedural continuous
      // assignments.
      return true;
  }
  return false;
}

bool AlwaysFfAdmitsCheckerVariableAssignment(CheckerVariableAssignment form) {
  switch (form) {
    case CheckerVariableAssignment::kNonblockingProcedural:
      // §17.7.1: in an always_ff procedure, only nonblocking assignments are
      // allowed.
      return true;
    case CheckerVariableAssignment::kBlockingProcedural:
    case CheckerVariableAssignment::kContinuous:
      // §17.7.1: a blocking assignment is excluded from an always_ff procedure,
      // and a continuous assignment is not a procedural assignment at all.
      return false;
  }
  return false;
}

bool CheckerVariableAssignmentReferenceIsLegal(CheckerVariableReference ref) {
  switch (ref) {
    case CheckerVariableReference::kSimpleName:
      // §17.7.1: naming a checker variable directly within its checker is the
      // legal way to assign it.
      return true;
    case CheckerVariableReference::kHierarchicalName:
      // §17.7.1: referencing a checker variable using its hierarchical name in
      // assignments (see §23.6) is illegal.
      return false;
  }
  return false;
}

bool FreeCheckerVariableAssignmentIsLegal(CheckerVariableAssignment form) {
  switch (form) {
    case CheckerVariableAssignment::kNonblockingProcedural:
      // §17.7.1: a free checker variable is assigned with the nonblocking
      // procedural form.
      return true;
    case CheckerVariableAssignment::kContinuous:
    case CheckerVariableAssignment::kBlockingProcedural:
      // §17.7.1: continuous assignments and blocking procedural assignments to
      // free checker variables are illegal.
      return false;
  }
  return false;
}

bool CheckerVariableAssignmentSiteIsLegal(CheckerVariableAssignmentSite site) {
  switch (site) {
    case CheckerVariableAssignmentSite::kDeclarationInitializer:
      // §17.7.1: a checker variable may be initialized in its declaration.
      return true;
    case CheckerVariableAssignmentSite::kInitialProcedure:
      // §17.7.1: a checker variable may not be assigned in an initial
      // procedure.
      return false;
  }
  return false;
}

bool CheckerVariableAssignmentRhsMayContainTriggered() {
  // §17.7.1: the right-hand side of a checker variable assignment may contain
  // the sequence method triggered (see §16.13.6).
  return true;
}

bool NonblockingAssignmentLhsMayBeFreeCheckerVariable() {
  // §17.7.1: the left-hand side of a nonblocking assignment may contain a free
  // checker variable.
  return true;
}

}  // namespace delta
