#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_validate_classes.h"

namespace delta {

void ElaboratorClassRules::RunPreElaborationClassValidations() {
  ValidateFinalClassExtension();

  ValidateWeakReferenceMembers();

  ValidateRestrictedScopePrefixInClasses();

  ValidateChainingConstructors();

  ValidateSuperRules();

  ValidateEmbeddedCovergroupAssign();

  ValidateDerivedCovergroupBase();

  ValidateConstClassProperties();

  ValidateVirtualMethodOverrides();

  ValidateAbstractClassRules();

  ValidateOutOfBlockDeclarations();

  ValidateNestedClassEnclosingAccess();

  ValidateInterfaceClassRules();

  // Clause 18: the class constraint rules are checked as one unit, against the
  // compilation unit and its typedef table.
  ClassConstraintValidator constraints(unit_, typedefs_, diag_);

  constraints.ValidateRandomVariableTypes();

  constraints.ValidateConstraintBlockNames();

  // 18.5.1: complete each prototype with its external block's body before the
  // checks on a constraint's contents, so those checks reach the block, and so
  // randomization applies it.
  constraints.CompleteExternalConstraints();

  constraints.ValidateForeachConstraintDims();

  constraints.ValidateDistConstraints();

  constraints.ValidateUniqueConstraints();

  constraints.ValidateSolveBeforeConstraints();

  constraints.ValidateSoftConstraintVariables();

  constraints.ValidateConstraintFunctionArgs();

  constraints.ValidateBuiltinRandomizationMethods();

  constraints.ValidateExternalConstraints();

  constraints.ValidateConstraintInheritance();

  ValidateForwardClassTypedefs();
}

}  // namespace delta
