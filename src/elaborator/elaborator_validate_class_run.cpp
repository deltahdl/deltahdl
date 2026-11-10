#include "elaborator/class_base_resolution.h"
#include "elaborator/class_default_specialization.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/elaborator_call_targets.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_param_restriction.h"
#include "elaborator/type_param_scope_prefix.h"

namespace delta {

void ElaboratorClassRules::RunPreElaborationClassValidations() {
  ValidateOutOfBlockDeclarations();

  ValidateFinalClassExtension();

  ValidateWeakReferenceMembers();

  ReportClassSpecializationsWithoutValues(*unit_, diag_);

  ReportBasesNamingNoClass(*unit_, diag_);

  ValidateThisOutsideModules();

  ValidateParameterizedScopeOutsideModules();

  ValidateClassHandleOpsOutsideModules();

  ValidateLocalProtectedAccessOutsideModules();

  ValidateLocalConstructorBases();

  ValidateRestrictedScopePrefixInClasses();

  ReportUnitSpecializations({typedefs_, unit_, class_names_}, diag_);

  ReportUnitScopeTypeParamErrors({typedefs_, unit_, class_names_}, diag_);

  ReportClassTypeParamsOutsideRestrictions({typedefs_, unit_, class_names_},
                                           diag_);

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

  ClassConstraintValidator constraints(unit_, typedefs_, diag_);

  constraints.ValidateRandomVariableTypes();

  constraints.ValidateConstraintBlockNames();

  constraints.CompleteExternalConstraints();

  constraints.ValidateForeachConstraintDims();

  constraints.ValidateDistConstraints();

  constraints.ValidateUniqueConstraints();
  constraints.ValidateConstraintOperandTypes();

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
  ValidateUnitClassCallArgs(*unit_, diag_);
}

}  // namespace delta
