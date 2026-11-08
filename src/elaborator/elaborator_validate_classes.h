#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_operations.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

struct ClassScope;

class ElaboratorClassRules : public ElaboratorOperationRules {
 protected:
  ElaboratorClassRules(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
      : ElaboratorOperationRules(arena, diag, unit) {}

  void RunPreElaborationClassValidations();

  void ValidateClassHandleOps(const ModuleDecl* decl);

  void WalkStmtsForClassHandleOps(const Stmt* s);
  void WalkSubroutinesForClassHandleOps(
      const std::vector<ModuleItem*>& items,
      const std::vector<const ClassDecl*>& classes = {});
  void ValidateClassHandleOpsOutsideModules();

  void ValidateClassHandleContAssign(const ModuleItem* item);

  void ValidateStaticMethodBodies(const ModuleDecl* decl);
  void ValidateStaticMethodsAmong(const std::vector<ModuleItem*>& items);
  void ValidateOneClassStaticMethods(const ClassDecl* cls);
  void ValidateNestedClassStaticMethods(const ClassDecl* cls);

  void ValidateThisUsage(const ModuleDecl* decl);
  void ValidateThisInItem(const ModuleItem* item);
  void ValidateThisOutsideModules();

  void BreakClassInheritanceCycles();

  void ValidateFinalClassExtension();

  void ValidateWeakReferenceMembers();

  void ApplyClassMethodAutomaticDefault();

  void ValidateChainingConstructors();
  void ValidateOneClassChainingCtor(const ClassDecl* cls);
  void ValidateOneClassDefaultKeyword(const ClassDecl* cls);

  void ValidateEmbeddedCovergroupAssign();
  void ValidateEmbeddedCovergroupRules();
  void ValidateClassMethodReads();
  void ValidateDerivedCovergroupBase();

  void ValidateLocalProtectedAccess(const ModuleDecl* decl);
  void ValidateLocalProtectedAccessOutsideModules();
  void ValidateLocalConstructorBases();
  void CheckVarInitConstructorAccess(const ModuleItem& item);
  void WalkSubroutinesForVisibility(
      const std::vector<ModuleItem*>& items,
      const std::vector<const ClassDecl*>& classes,
      const std::unordered_map<std::string_view, std::string_view>&
          scope_types);

  void ValidateConstClassProperties();
  void ValidateConstPropertyWritesFromOutside(const ModuleDecl* decl);

  void ValidateVirtualMethodOverrides();
  void ValidateOneMethodOverride(const ClassDecl* cls, const ClassMember* m);

  void ValidateAbstractClassRules();
  void ValidateAbstractClassUnimplemented(const ClassDecl* cls);
  void ValidateSuperRules();

  void ValidateOutOfBlockDeclarations();

  void ValidateNestedClassEnclosingAccess();

  void ValidateParameterizedScopeResolution(const ModuleDecl* decl);
  void ValidateParameterizedScopeOutsideModules();
  void CheckParamScopeInItem(const ModuleItem& item);
  void CheckParamScopeInSubroutine(
      const ModuleItem& sub,
      const std::unordered_set<std::string_view>& allowed);
  void CheckParamScopeInClass(const ClassDecl& cls,
                              std::unordered_set<std::string_view> allowed);

  void ValidateRestrictedScopePrefixUsage(const ModuleDecl* decl);

  void ValidateRestrictedScopePrefixInClasses();

  void ValidateInterfaceClassRules();

  void ValidateForwardClassTypedefs();

  void ValidateForwardTypedefsInScope(const std::vector<ModuleItem*>& items);

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

 private:
  std::unordered_set<const ClassDecl*> static_method_bodies_checked_;
  std::unordered_set<std::string_view> keyword_typed_params_;
};

}  // namespace delta
