#pragma once

#include <cstdint>

namespace delta {

// §16.15 governs how the disable condition of a concurrent assertion is
// resolved, including the scoping of a `default disable iff` declaration. The
// grammar production itself is borrowed from A.1.4 and parsed elsewhere; the
// rules modeled here are the elaboration-time semantics defined by §16.15.

// §16.15: a default disable iff declaration may be declared within a module,
// interface, or program declaration, or within a generate block.
enum class DisableIffScopeKind : uint8_t {
  kModule,
  kInterface,
  kProgram,
  kGenerateBlock,
};

// §16.15: kinds of boundary the default disable condition may meet as it
// propagates from the declaring scope toward a concurrent assertion. The
// default extends across nested *declarations* and nested generate blocks, but
// not across the boundary of an elaborated *instance*.
enum class ScopeBoundaryKind : uint8_t {
  kNestedModuleDecl,
  kNestedInterfaceDecl,
  kNestedProgramDecl,
  kNestedGenerateBlock,
  kModuleInstance,
  kInterfaceInstance,
  kProgramInstance,
};

// §16.15: how an assertion's disable condition is determined, one case per
// resolution rule a), b), c).
enum class DisableConditionSource : uint8_t {
  // Rule a): the assertion carries its own disable iff clause.
  kExplicitClause,
  // Rule b): no clause, but the assertion lies within a default disable iff
  // scope, so the condition is inferred from that declaration.
  kInheritedDefault,
  // Rule c): no clause and no enclosing default; no inference is performed,
  // which is equivalent to a 1'b0 (never) disable condition.
  kNoneEquivalentToFalse,
};

// §16.15: position of a default disable iff declaration relative to an
// assertion that shares its scope.
enum class DeclarationPosition : uint8_t {
  kBeforeAssertion,
  kAfterAssertion,
};

// §16.15: which scope is used to resolve signals named in the default disable
// iff declaration.
enum class DisableSignalScope : uint8_t {
  // The scope in which the default disable iff was declared.
  kDeclaringScope,
  // The scope of an individual assertion that inherits the default.
  kAssertionScope,
};

// §16.15: every modeled declaration site (module, interface, program, generate
// block) is a legal place for a default disable iff declaration.
bool DefaultDisableIffAllowedInScope(DisableIffScopeKind scope);

// §16.15: the default disable condition extends into nested module, interface,
// and program declarations and into nested generate blocks, but does not extend
// into any instances of modules, interfaces, or programs. Returns true when the
// default propagates across the given boundary.
bool DefaultDisablePropagatesAcross(ScopeBoundaryKind boundary);

// §16.15: if a nested scope declares its own default disable iff, that
// declaration applies within the nested scope and overrides any default from
// outside. Returns true when the nested scope's own declaration governs.
bool NestedDefaultOverridesOuter(bool nested_scope_has_own_default);

// §16.15: signals referenced in the disable iff declaration that are resolved
// using scopes are resolved from the scope of the declaration.
DisableSignalScope DefaultDisableSignalResolutionScope();

// §16.15: the effect of a default disable iff is independent of the position of
// the declaration within its scope. An assertion sharing the scope is governed
// by the declaration whether the declaration textually precedes or follows it.
bool AssertionGovernedBySameScopeDefault(DeclarationPosition position);

// §16.15 resolution rules a), b), c). The result depends only on whether the
// assertion has its own clause and whether it lies within a default disable iff
// scope; it does not depend on the position of the default disable iff
// declaration within that scope.
DisableConditionSource ResolveDisableConditionSource(
    bool assertion_has_explicit_disable_iff, bool within_default_disable_scope);

}  // namespace delta
