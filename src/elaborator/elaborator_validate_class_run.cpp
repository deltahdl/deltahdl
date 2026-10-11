#include "elaborator/class_base_resolution.h"
#include "elaborator/class_default_specialization.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/elaborator_call_targets.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_validate_classes.h"

namespace delta {

void ElaboratorClassRules::RunPreElaborationClassValidations() {
  // §8.24: first, so that each extern prototype is linked to the out-of-block
  // declaration defining it before any rule below reads a method's body
  // through MethodBody.
  ValidateOutOfBlockDeclarations();

  ValidateFinalClassExtension();

  ValidateWeakReferenceMembers();

  ReportUnadornedClassesWithoutDefaults(*unit_, diag_);

  ReportBasesNamingNoClass(*unit_, diag_);

  ValidateThisOutsideModules();

  ValidateParameterizedScopeOutsideModules();

  ValidateClassHandleOpsOutsideModules();

  ValidateLocalProtectedAccessOutsideModules();

  ValidateLocalConstructorBases();

  ValidateRestrictedScopePrefixInClasses();

  ValidateChainingConstructors();

  ValidateSuperRules();

  ValidateEmbeddedCovergroupAssign();

  ValidateEmbeddedCovergroupRules();

  ValidateClassMethodReads();

  ValidateDerivedCovergroupBase();

  ValidateConstClassProperties();

  ValidateVirtualMethodOverrides();

  ValidateAbstractClassRules();

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

void ElaboratorClassRules::ValidateClassMethodReads() {
  ReportClassMethodUnresolved(unit_, diag_);
  ReportClassMethodCalls(*unit_, diag_);
}

}  // namespace delta
