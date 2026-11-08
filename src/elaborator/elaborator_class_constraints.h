#pragma once

#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"

namespace delta {

class ClassConstraintValidator {
 public:
  ClassConstraintValidator(const CompilationUnit* unit,
                           const TypedefMap& typedefs, DiagEngine& diag)
      : unit_(unit), typedefs_(typedefs), diag_(diag) {}

  void ValidateRandomVariableTypes();
  void ValidateOneClassRandomVariables(const ClassDecl* cls);

  void ValidateConstraintBlockNames();
  void ValidateOneClassConstraintNames(const ClassDecl* cls);

  void ValidateForeachConstraintDims();
  void ValidateOneClassForeachConstraintDims(const ClassDecl* cls);

  void ValidateDistConstraints();
  void ValidateOneClassDistConstraints(const ClassDecl* cls);

  void ValidateUniqueConstraints();
  void ValidateOneClassUniqueConstraints(const ClassDecl* cls);

  void ValidateConstraintOperandTypes();

  void ValidateSolveBeforeConstraints();
  void ValidateOneClassSolveBeforeConstraints(const ClassDecl* cls);

  void ValidateSoftConstraintVariables();
  void ValidateOneClassSoftConstraintVariables(const ClassDecl* cls);

  void ValidateConstraintFunctionArgs();
  void ValidateOneClassConstraintFunctionArgs(const ClassDecl* cls);

  void ValidateBuiltinRandomizationMethods();
  void ValidateOneClassBuiltinMethods(const ClassDecl* cls);

  void ValidateExternalConstraints();
  void ValidateOneClassExternalConstraints(const ClassDecl* cls);
  void CompleteExternalConstraints();

  void ValidateConstraintInheritance();
  void ValidateOneConstraintOverride(const ClassDecl* cls,
                                     const ClassMember* m);
  void ValidateNonAbstractPureConstraints(const ClassDecl* cls);
  void ValidateConstraintSpecifierParity(const ClassDecl* cls,
                                         const ClassMember* m);

 private:
  const CompilationUnit* unit_;
  const TypedefMap& typedefs_;
  DiagEngine& diag_;
};

void ValidateInlineUniqueGroups(const Expr* call, const ClassDecl* cls,
                                const CompilationUnit* unit, DiagEngine& diag);

void ValidateInlineConstraintOperands(const Expr* call, const ClassDecl* cls,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag);

void ValidateInlineQualifiedNames(const Expr* call, const ClassDecl* cls,
                                  const CompilationUnit* unit,
                                  DiagEngine& diag);

void ValidateInlineUniqueReceivers(const CompilationUnit* unit,
                                   DiagEngine& diag);

}  // namespace delta
