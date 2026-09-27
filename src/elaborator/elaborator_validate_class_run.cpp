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

  constraints.ValidateForeachConstraintDims();

  constraints.ValidateDistConstraints();

  constraints.ValidateUniqueConstraints();

  constraints.ValidateSolveBeforeConstraints();

  constraints.ValidateSoftConstraintVariables();

  constraints.ValidateConstraintFunctionArgs();

  constraints.ValidateBuiltinRandomizationMethods();

  constraints.ValidateExternalConstraints();

  // 18.5.1: once the external blocks are validated, complete each prototype by
  // attaching its external block's relations so randomization applies them.
  constraints.CompleteExternalConstraints();

  constraints.ValidateConstraintInheritance();

  ValidateForwardClassTypedefs();
}

}  // namespace delta
