#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// Clause 18: the constraint rules a design's classes are checked against
// before elaboration -- random variable types, constraint block names, the
// bodies of foreach/dist/unique/solve...before/soft constraints, the functions
// a constraint may call, the built-in randomization method names, and the
// external-block and inheritance rules on constraint prototypes. They read the
// compilation unit and its typedef table and report through the diagnostic
// engine, so they form a unit of their own rather than further members of the
// elaborator.
class ClassConstraintValidator {
 public:
  ClassConstraintValidator(const CompilationUnit* unit,
                           const TypedefMap& typedefs, DiagEngine& diag)
      : unit_(unit), typedefs_(typedefs), diag_(diag) {}

  // 18.4: random variable type rules for rand/randc class properties.
  void ValidateRandomVariableTypes();
  void ValidateOneClassRandomVariables(const ClassDecl* cls);

  // 18.5: constraint block names shall be unique within a class.
  void ValidateConstraintBlockNames();
  void ValidateOneClassConstraintNames(const ClassDecl* cls);

  // 18.5.7.1: in a foreach iterative constraint the number of loop variables
  // shall not exceed the number of dimensions of the iterated array.
  void ValidateForeachConstraintDims();
  void ValidateOneClassForeachConstraintDims(const ClassDecl* cls);

  // 18.5.3: a real-valued range in a distribution shall use the :/ operator and
  // shall specify a weight.
  void ValidateDistConstraints();
  void ValidateOneClassDistConstraints(const ClassDecl* cls);

  // 18.5.4: the range_list of a uniqueness constraint shall contain only
  // expressions that denote singular or array variables.
  void ValidateUniqueConstraints();
  void ValidateOneClassUniqueConstraints(const ClassDecl* cls);
  // 18.5.5: one member of a uniqueness constraint's variable group -- it shall
  // denote a singular or array variable, of integral or real type.
  void ValidateOneUniqueConstraintMember(
      const Expr* mem,
      const std::unordered_map<std::string_view, const ClassMember*>&
          properties);

  // 18.5.9: a solve...before ordering constraint may name only rand variables
  // (never randc), each integral or real, with no circular dependency.
  void ValidateSolveBeforeConstraints();
  void ValidateOneClassSolveBeforeConstraints(const ClassDecl* cls);
  bool IsSolveOrderableType(const DataType& dt) const;

  // 18.5.13.1: a soft constraint may be specified only on a random variable;
  // it may not be specified for a randc variable.
  void ValidateSoftConstraintVariables();
  void ValidateOneClassSoftConstraintVariables(const ClassDecl* cls);

  // 18.5.11: a function called from a constraint expression shall not have
  // output, inout, or non-const ref arguments (const ref is allowed).
  void ValidateConstraintFunctionArgs();
  void ValidateOneClassConstraintFunctionArgs(const ClassDecl* cls);

  // 18.8: rand_mode() is a built-in method and cannot be overridden, so a
  // class shall not declare a method of that name.
  void ValidateBuiltinRandomizationMethods();
  void ValidateOneClassBuiltinMethods(const ClassDecl* cls);

  // 18.5.1: external constraint blocks complete constraint prototypes.
  void ValidateExternalConstraints();
  void ValidateOneClassExternalConstraints(const ClassDecl* cls);
  void CompleteExternalConstraints();

  // 18.5.2: constraint inheritance and override specifiers.
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

}  // namespace delta
