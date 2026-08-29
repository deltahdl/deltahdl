#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_operations.h"
#include "parser/ast.h"

namespace delta {

struct ClassScope;

// The rules a class declaration has to keep, whatever module, package or
// compilation unit it is written in. Clause 8 states most of them -- §8.4 on
// the operators a class handle admits, §8.10 on static methods and §8.11 on
// `this`, §8.17 on chaining constructors, §8.18 on local and protected
// members, §8.20 on virtual method overrides, §8.21 on abstract classes,
// §8.24 on out-of-block declarations and §8.26 on interface classes among
// them -- and §6.18's forward typedef, §6.20.3's type parameter as a scope
// resolution prefix and §19.4's embedded covergroup state the rest. What they
// share is the question they ask: whether one class declaration is well
// formed, given the other classes the compilation unit holds and the types
// their members name.
//
// They are a class of their own because src/elaborator/elaborator.h reached
// the 950 lines at which assert-no-oversized-source-files in
// .github/workflows/deltahdl.yml asks for a split, and this is the group whose
// boundary the standard draws for itself: no declaration here elaborates
// anything, and none of them reads an RtlirModule. Most of the definitions
// were already gathered in the src/elaborator/elaborator_validate_class*.cpp
// files and in src/elaborator/elaborator_validate_static_methods.cpp.
// RunPreElaborationClassValidations stands in src/elaborator/elaborator.cpp
// and the two §6.18 forward-typedef checks in
// src/elaborator/elaborator_scope_rules_enclosing.cpp, each left in the file
// it was written in, since the file a definition stands in does not decide
// which class declares it.
//
// This derives from ElaboratorOperationRules in
// src/elaborator/elaborator_validate_operations.h, and Elaborator in
// src/elaborator/elaborator.h derives from this. That is one chain rather than
// two bases, so a single ElaboratorData subobject carries the elaborator's
// state and these checks report through the same `diag_` the rest of the
// elaborator reports through. Elaborator reaches them the way a derived class
// reaches any protected base member, and nothing here calls a member of
// Elaborator, which a base cannot reach.
// Elaborator::ValidateClassMethodBodies is the one class rule that stayed
// behind for that reason: it calls Elaborator::ValidateFunctionBody, the §13
// rule on the body of a subroutine.
class ElaboratorClassRules : public ElaboratorOperationRules {
 protected:
  ElaboratorClassRules(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
      : ElaboratorOperationRules(arena, diag, unit) {}

  // Clause 8 and Clause 18: the checks over the class declarations of the
  // compilation unit, run as one step of RunPreElaborationValidations and in
  // the position it calls them from.
  void RunPreElaborationClassValidations();

  void ValidateClassHandleOps(const ModuleDecl* decl);

  void WalkStmtsForClassHandleOps(const Stmt* s);

  void ValidateClassHandleContAssign(const ModuleItem* item);

  void ValidateStaticMethodBodies(const ModuleDecl* decl);
  void ValidateOneClassStaticMethods(const ClassDecl* cls);

  void ValidateThisUsage(const ModuleDecl* decl);
  void ValidateThisInItem(const ModuleItem* item);

  void ValidateFinalClassExtension();

  void ValidateWeakReferenceMembers();

  void ApplyClassMethodAutomaticDefault();

  void ValidateChainingConstructors();
  void ValidateOneClassChainingCtor(const ClassDecl* cls);
  void ValidateOneClassDefaultKeyword(const ClassDecl* cls);

  void ValidateEmbeddedCovergroupAssign();
  void ValidateDerivedCovergroupBase();

  void ValidateLocalProtectedAccess(const ModuleDecl* decl);

  void ValidateConstClassProperties();

  void ValidateVirtualMethodOverrides();
  void ValidateOneMethodOverride(const ClassDecl* cls, const ClassMember* m);

  void ValidateAbstractClassRules();
  void ValidateAbstractClassUnimplemented(const ClassDecl* cls);
  void ValidateSuperRules();

  void ValidateOutOfBlockDeclarations();

  void ValidateParameterizedScopeResolution(const ModuleDecl* decl);

  // §8.23: an incomplete forward type, a type defined by an interface-based
  // typedef (§6.18) and a type parameter (§6.20.3) may prefix the class scope
  // resolution operator only in a typedef declaration, the type operator, or a
  // type parameter assignment, never in an ordinary expression.
  void ValidateRestrictedScopePrefixUsage(const ModuleDecl* decl);

  // §6.20.3: the same restriction over the body of a class declared at the
  // outermost level, whose enclosing scope is the compilation unit. This is the
  // position the subclause writes its own example in, `C::T x;` in the body of
  // `class P#(type C)`.
  void ValidateRestrictedScopePrefixInClasses();

  // §6.20.3: a type parameter used as a class scope resolution prefix shall
  // resolve to a class.
  void ValidateTypeParamScopePrefixResolvesToClass(const ModuleDecl* decl);

  void ValidateInterfaceClassRules();

  void ValidateForwardClassTypedefs();

  void ValidateForwardTypedefsInScope(const ModuleDecl* decl);

  void ValidateForwardTypedefScopePrefix(const ModuleDecl* decl);
  void ValidateInterfaceClassMembers(const ClassDecl* cls);
  void ValidateInterfaceClassInheritance(const ClassDecl* cls,
                                         const ClassScope& scope);
  void ValidateRegularClassInheritance(const ClassDecl* cls,
                                       const ClassScope& scope);
  void ValidateImplementsInterfaceMethods(const ClassDecl* cls);
  void ValidateVirtualClassInterfaceObligations(const ClassDecl* cls,
                                                const ScopeMap& params);
  void ValidateImplementsTypeAccess(const ClassDecl* cls,
                                    const ScopeMap& params);
  void CheckImplementsTypeAccessOfMember(
      const ClassMember* m,
      const std::unordered_map<std::string_view, std::string_view>&
          owning_iface,
      const std::unordered_set<std::string_view>& visible);
  void CheckImplementsTypeAccessOfType(
      const DataType& dt, SourceLoc loc,
      const std::unordered_map<std::string_view, std::string_view>&
          owning_iface,
      const std::unordered_set<std::string_view>& visible);
};

}  // namespace delta
