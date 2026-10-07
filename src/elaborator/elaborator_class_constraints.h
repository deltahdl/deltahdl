#pragma once

#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"

namespace delta {

// Clause 18: the constraint rules a design's classes are checked against
// before elaboration -- random variable types, constraint block names, the
// bodies of foreach/dist/unique/solve...before/soft constraints, the functions
// a constraint may call, the built-in randomization method names, and the
// external-block and inheritance rules on constraint prototypes. They read the
// compilation unit and its typedef table and report through the diagnostic
// engine, so they form a unit of their own rather than further members of the
// elaborator. The per-class rules walk every class the unit declares, in a
// module, interface, program, checker or package as well as at the top of a
// file (AllClassDecls in elaborator_helpers.h); the external-block rules pair
// each block with the class of the scope it shares with it.
class ClassConstraintValidator {
 public:
  ClassConstraintValidator(const CompilationUnit* unit,
                           const TypedefMap& typedefs, DiagEngine& diag)
      : unit_(unit), typedefs_(typedefs), diag_(diag) {}

  // 18.4: random variable type rules for rand/randc class properties.
  void ValidateRandomVariableTypes();
  void ValidateOneClassRandomVariables(const ClassDecl* cls);

  // 18.5: no two constraint blocks of one class may share a name.
  void ValidateConstraintBlockNames();
  void ValidateOneClassConstraintNames(const ClassDecl* cls);

  // 18.5.7.1: a foreach iterative constraint names no more loop variables than
  // the iterated array has dimensions.
  void ValidateForeachConstraintDims();
  void ValidateOneClassForeachConstraintDims(const ClassDecl* cls);

  // 18.5.3: a real-valued range in a distribution needs an explicit weight,
  // given with the :/ operator.
  void ValidateDistConstraints();
  void ValidateOneClassDistConstraints(const ClassDecl* cls);

  // 18.5.4: each expression in a uniqueness constraint's range_list denotes a
  // singular or array variable.
  void ValidateUniqueConstraints();
  void ValidateOneClassUniqueConstraints(const ClassDecl* cls);

  // 18.5.9: a solve...before ordering constraint may name only rand variables
  // (never randc), each integral or real, with no circular dependency.
  void ValidateSolveBeforeConstraints();
  void ValidateOneClassSolveBeforeConstraints(const ClassDecl* cls);

  // 18.5.13.1: a soft constraint applies to random variables alone, and never
  // to a randc variable.
  void ValidateSoftConstraintVariables();
  void ValidateOneClassSoftConstraintVariables(const ClassDecl* cls);

  // 18.5.11: a function called from a constraint expression takes only input
  // and const ref arguments.
  void ValidateConstraintFunctionArgs();
  void ValidateOneClassConstraintFunctionArgs(const ClassDecl* cls);

  // 18.8: rand_mode() is predefined and no class may override it, so no class
  // may declare a method of that name.
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

// 18.5.4 with 18.7: checks each member of the uniqueness groups in the inline
// constraint block of `call`, a randomize() with call on an object of class
// `cls`, as the groups of the class's own constraint blocks are checked. Does
// nothing for a call without an inline block.
void ValidateInlineUniqueGroups(const Expr* call, const ClassDecl* cls,
                                const CompilationUnit* unit, DiagEngine& diag);

// 18.5.4 with 18.7: checks the inline uniqueness groups of every randomize()
// with call in the unit against the class of the object it randomizes, found
// from the static type of the receiver in the scope the call stands in.
// Defined in elaborator_validate_inline_unique.cpp.
void ValidateInlineUniqueReceivers(const CompilationUnit* unit,
                                   DiagEngine& diag);

}  // namespace delta
