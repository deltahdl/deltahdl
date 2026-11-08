#include "elaborator/disable_iff_resolution.h"

#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

void CheckDefaultDisableInScope(const std::vector<ModuleItem*>& items,
                                DiagEngine& diag);

void CheckGenerateItemScopes(const ModuleItem* item, DiagEngine& diag) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      CheckDefaultDisableInScope(item->gen_body, diag);
      if (item->gen_else) CheckGenerateItemScopes(item->gen_else, diag);
      break;
    case ModuleItemKind::kGenerateFor:
      CheckDefaultDisableInScope(item->gen_body, diag);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items)
        CheckDefaultDisableInScope(ci.body, diag);
      break;
    default:
      break;
  }
}

void CheckDefaultDisableInScope(const std::vector<ModuleItem*>& items,
                                DiagEngine& diag) {
  int count = 0;
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kDefaultDisableIff) continue;
    if (++count == 2) {
      diag.Error(item->loc,
                 "only one default disable iff declaration is allowed per "
                 "scope",
                 Subclause("16.15"));
    }
  }
  for (const auto* item : items) CheckGenerateItemScopes(item, diag);
}

}  // namespace

void Elaborator::ValidateDuplicateDefaultDisableIff(const ModuleDecl* decl) {
  CheckDefaultDisableInScope(decl->items, diag_);
}

bool DefaultDisableIffAllowedInScope(DisableIffScopeKind scope) {
  switch (scope) {
    case DisableIffScopeKind::kModule:
    case DisableIffScopeKind::kInterface:
    case DisableIffScopeKind::kProgram:
    case DisableIffScopeKind::kGenerateBlock:
      return true;
  }
  return false;
}

bool DefaultDisablePropagatesAcross(ScopeBoundaryKind boundary) {
  switch (boundary) {
    case ScopeBoundaryKind::kNestedModuleDecl:
    case ScopeBoundaryKind::kNestedInterfaceDecl:
    case ScopeBoundaryKind::kNestedProgramDecl:
    case ScopeBoundaryKind::kNestedGenerateBlock:
      return true;
    case ScopeBoundaryKind::kModuleInstance:
    case ScopeBoundaryKind::kInterfaceInstance:
    case ScopeBoundaryKind::kProgramInstance:
      return false;
  }
  return false;
}

bool NestedDefaultOverridesOuter(bool nested_scope_has_own_default) {
  return nested_scope_has_own_default;
}

DisableSignalScope DefaultDisableSignalResolutionScope() {
  return DisableSignalScope::kDeclaringScope;
}

bool AssertionGovernedBySameScopeDefault(DeclarationPosition position) {
  switch (position) {
    case DeclarationPosition::kBeforeAssertion:
    case DeclarationPosition::kAfterAssertion:
      return true;
  }
  return false;
}

DisableConditionSource ResolveDisableConditionSource(
    bool assertion_has_explicit_disable_iff,
    bool within_default_disable_scope) {
  if (assertion_has_explicit_disable_iff)
    return DisableConditionSource::kExplicitClause;
  if (within_default_disable_scope)
    return DisableConditionSource::kInheritedDefault;
  return DisableConditionSource::kNoneEquivalentToFalse;
}

Expr* DeclaredDefaultDisableIff(const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kDefaultDisableIff) {
      return item->init_expr;
    }
  }
  return nullptr;
}

}  // namespace delta
