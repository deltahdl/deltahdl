#pragma once

#include <cstdint>
#include <vector>

namespace delta {

struct Expr;
struct ModuleItem;

enum class DisableIffScopeKind : uint8_t {
  kModule,
  kInterface,
  kProgram,
  kGenerateBlock,
};

enum class ScopeBoundaryKind : uint8_t {
  kNestedModuleDecl,
  kNestedInterfaceDecl,
  kNestedProgramDecl,
  kNestedGenerateBlock,
  kModuleInstance,
  kInterfaceInstance,
  kProgramInstance,
};

enum class DisableConditionSource : uint8_t {
  kExplicitClause,
  kInheritedDefault,
  kNoneEquivalentToFalse,
};

enum class DeclarationPosition : uint8_t {
  kBeforeAssertion,
  kAfterAssertion,
};

enum class DisableSignalScope : uint8_t {
  kDeclaringScope,
  kAssertionScope,
};

bool DefaultDisableIffAllowedInScope(DisableIffScopeKind scope);

bool DefaultDisablePropagatesAcross(ScopeBoundaryKind boundary);

bool NestedDefaultOverridesOuter(bool nested_scope_has_own_default);

DisableSignalScope DefaultDisableSignalResolutionScope();

bool AssertionGovernedBySameScopeDefault(DeclarationPosition position);

DisableConditionSource ResolveDisableConditionSource(
    bool assertion_has_explicit_disable_iff, bool within_default_disable_scope);

Expr* DeclaredDefaultDisableIff(const std::vector<ModuleItem*>& items);

}  // namespace delta
