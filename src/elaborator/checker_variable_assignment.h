#ifndef DELTA_ELABORATOR_CHECKER_VARIABLE_ASSIGNMENT_H
#define DELTA_ELABORATOR_CHECKER_VARIABLE_ASSIGNMENT_H

#include <cstdint>

namespace delta {

// §17.7.1 governs how checker variables may be assigned. The helpers here model
// only the rules the text of §17.7.1 states directly: which assignment forms a
// checker variable admits, the restriction that narrows an always_ff procedure
// to nonblocking assignments, the illegality of assigning through a
// hierarchical name, the illegality of continuous and blocking assignments to a
// free checker variable, where a checker variable may and may not receive a
// value, and the two allowances about the assignment's right- and left-hand
// sides. The hierarchical-name machinery is owned by §23.6 and the triggered
// method by §16.13.6; this file only records how §17.7.1 scopes those onto
// checker variable assignments.

// §17.7.1: the assignment forms that may target a checker variable.
enum class CheckerVariableAssignment : uint8_t {
  kBlockingProcedural,     // a blocking procedural assignment
  kNonblockingProcedural,  // a nonblocking procedural assignment
  kContinuous,             // a non-procedural continuous assignment
};

// §17.7.1: a checker variable may be assigned using blocking and nonblocking
// procedural assignments, or non-procedural continuous assignments. Each of the
// three forms is therefore an available way to assign a checker variable.
bool CheckerVariableAssignmentFormIsAvailable(CheckerVariableAssignment form);

// §17.7.1: in an always_ff procedure, only nonblocking assignments are allowed.
// A blocking procedural assignment is therefore not allowed there; a continuous
// assignment is not a procedural assignment and so cannot appear in the
// procedure either.
bool AlwaysFfAdmitsCheckerVariableAssignment(CheckerVariableAssignment form);

// §17.7.1: how a checker variable is named on the left-hand side of an
// assignment.
enum class CheckerVariableReference : uint8_t {
  kSimpleName,        // the variable named within its own checker
  kHierarchicalName,  // the variable reached through a hierarchical path
};

// §17.7.1: referencing a checker variable using its hierarchical name in
// assignments (see §23.6) is illegal. A simple, in-checker reference is the
// legal way to name a checker variable being assigned.
bool CheckerVariableAssignmentReferenceIsLegal(CheckerVariableReference ref);

// §17.7.1: continuous assignments and blocking procedural assignments to free
// checker variables are illegal. For a free checker variable only the
// nonblocking procedural form remains legal.
bool FreeCheckerVariableAssignmentIsLegal(CheckerVariableAssignment form);

// §17.7.1: the places where a checker variable may receive a value.
enum class CheckerVariableAssignmentSite : uint8_t {
  kInitialProcedure,        // an assignment inside an initial procedure
  kDeclarationInitializer,  // an initializer in the variable's declaration
};

// §17.7.1: a checker variable may not be assigned in an initial procedure, but
// it may be initialized in its declaration. Assignment is therefore legal at
// the declaration initializer and illegal inside an initial procedure.
bool CheckerVariableAssignmentSiteIsLegal(CheckerVariableAssignmentSite site);

// §17.7.1: the right-hand side of a checker variable assignment may contain the
// sequence method triggered (see §16.13.6).
bool CheckerVariableAssignmentRhsMayContainTriggered();

// §17.7.1: the left-hand side of a nonblocking assignment may contain a free
// checker variable.
bool NonblockingAssignmentLhsMayBeFreeCheckerVariable();

}  // namespace delta

#endif  // DELTA_ELABORATOR_CHECKER_VARIABLE_ASSIGNMENT_H
