#include "elaborator/disable_iff_resolution.h"

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "parser/ast.h"

namespace delta {

namespace {

void CheckDefaultDisableInScope(const std::vector<ModuleItem*>& items,
                                DiagEngine& diag);

// §16.15: each generate block forms its own scope for the default-disable
// uniqueness rule, so recurse into every block nested in `item`. A conditional
// generate's then-block and each else arm, a loop generate's body, and every
// case generate arm are independent scopes.
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

// §16.15: more than one default disable iff declaration directly within one
// scope shall be an error. Count the declarations that belong to this scope and
// flag the surplus, then descend into the generate blocks it contains, each of
// which is checked as its own separate scope.
void CheckDefaultDisableInScope(const std::vector<ModuleItem*>& items,
                                DiagEngine& diag) {
  int count = 0;
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kDefaultDisableIff) continue;
    if (++count == 2) {
      diag.Error(item->loc,
                 "only one default disable iff declaration is allowed per "
                 "scope");
    }
  }
  for (const auto* item : items) CheckGenerateItemScopes(item, diag);
}

}  // namespace

void Elaborator::ValidateDuplicateDefaultDisableIff(const ModuleDecl* decl) {
  // §16.15: the uniqueness rule applies within a module, interface, or program
  // declaration and, independently, within each generate block. The module body
  // is one scope; the recursion treats every nested generate block as another.
  CheckDefaultDisableInScope(decl->items, diag_);
}

bool DefaultDisableIffAllowedInScope(DisableIffScopeKind scope) {
  // §16.15: a default disable iff may be declared within a module, interface,
  // or program declaration, or within a generate block. All four sites are
  // legal.
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
    // §16.15: the default extends to nested module, interface, and program
    // declarations and to nested generate blocks.
    case ScopeBoundaryKind::kNestedModuleDecl:
    case ScopeBoundaryKind::kNestedInterfaceDecl:
    case ScopeBoundaryKind::kNestedProgramDecl:
    case ScopeBoundaryKind::kNestedGenerateBlock:
      return true;
    // §16.15: the scope does not extend into any instances of modules,
    // interfaces, or programs.
    case ScopeBoundaryKind::kModuleInstance:
    case ScopeBoundaryKind::kInterfaceInstance:
    case ScopeBoundaryKind::kProgramInstance:
      return false;
  }
  return false;
}

bool NestedDefaultOverridesOuter(bool nested_scope_has_own_default) {
  // §16.15: a default disable iff in a nested scope applies within that scope
  // and overrides any default disable iff from outside.
  return nested_scope_has_own_default;
}

DisableSignalScope DefaultDisableSignalResolutionScope() {
  // §16.15: scoped signals named in the disable iff declaration resolve from
  // the scope of the declaration, not from each inheriting assertion's scope.
  return DisableSignalScope::kDeclaringScope;
}

bool AssertionGovernedBySameScopeDefault(DeclarationPosition position) {
  // §16.15: the position of the declaration within the scope is irrelevant; an
  // assertion in the same scope is governed by the default disable iff whether
  // the declaration appears before or after it.
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
  // §16.15 rule a): an explicit disable iff clause wins and any default disable
  // iff is ignored for this assertion.
  if (assertion_has_explicit_disable_iff)
    return DisableConditionSource::kExplicitClause;
  // §16.15 rule b): no clause, but within a default disable iff scope, so the
  // condition is inferred from the default declaration.
  if (within_default_disable_scope)
    return DisableConditionSource::kInheritedDefault;
  // §16.15 rule c): otherwise no inference is performed, equivalent to a 1'b0
  // disable condition.
  return DisableConditionSource::kNoneEquivalentToFalse;
}

}  // namespace delta
