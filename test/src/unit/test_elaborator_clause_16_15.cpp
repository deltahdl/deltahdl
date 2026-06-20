#include <gtest/gtest.h>

#include "elaborator/disable_iff_resolution.h"

using namespace delta;

namespace {

TEST(DisableIffResolution, DeclarationSitesAreLegal) {
  // §16.15: a default disable iff may be declared within a module, interface,
  // or program declaration, or within a generate block.
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kModule));
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kInterface));
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kProgram));
  EXPECT_TRUE(
      DefaultDisableIffAllowedInScope(DisableIffScopeKind::kGenerateBlock));
}

TEST(DisableIffResolution, MultipleInSameScopeIsError) {
  // §16.15: more than one default disable iff declaration within the same
  // scope shall be an error; zero or one is allowed.
  EXPECT_FALSE(MultipleDefaultDisableIffIsError(0));
  EXPECT_FALSE(MultipleDefaultDisableIffIsError(1));
  EXPECT_TRUE(MultipleDefaultDisableIffIsError(2));
  EXPECT_TRUE(MultipleDefaultDisableIffIsError(3));
}

TEST(DisableIffResolution, ExtendsIntoNestedDeclarationsAndGenerateBlocks) {
  // §16.15: the default extends to nested module, interface, and program
  // declarations and to nested generate blocks.
  EXPECT_TRUE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kNestedModuleDecl));
  EXPECT_TRUE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kNestedInterfaceDecl));
  EXPECT_TRUE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kNestedProgramDecl));
  EXPECT_TRUE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kNestedGenerateBlock));
}

TEST(DisableIffResolution, DoesNotExtendIntoInstances) {
  // §16.15: the scope does not extend into any instances of modules,
  // interfaces, or programs.
  EXPECT_FALSE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kModuleInstance));
  EXPECT_FALSE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kInterfaceInstance));
  EXPECT_FALSE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kProgramInstance));
}

TEST(DisableIffResolution, NestedDeclarationOverridesOuter) {
  // §16.15: a nested scope's own default disable iff overrides any default
  // from outside; without one the nested scope inherits the enclosing default.
  EXPECT_TRUE(NestedDefaultOverridesOuter(true));
  EXPECT_FALSE(NestedDefaultOverridesOuter(false));
}

TEST(DisableIffResolution, SignalsResolveInDeclaringScope) {
  // §16.15: scoped signals named in the disable iff declaration are resolved
  // from the scope of the declaration.
  EXPECT_EQ(DefaultDisableSignalResolutionScope(),
            DisableSignalScope::kDeclaringScope);
}

TEST(DisableIffResolution, RuleAExplicitClauseWins) {
  // §16.15 rule a): an explicit disable iff clause is used and any default
  // disable iff is ignored, regardless of whether a default is in scope.
  EXPECT_EQ(ResolveDisableConditionSource(true, true),
            DisableConditionSource::kExplicitClause);
  EXPECT_EQ(ResolveDisableConditionSource(true, false),
            DisableConditionSource::kExplicitClause);
}

TEST(DisableIffResolution, RuleBInheritsDefaultInScope) {
  // §16.15 rule b): no explicit clause but within a default disable iff scope
  // infers the condition from the default declaration.
  EXPECT_EQ(ResolveDisableConditionSource(false, true),
            DisableConditionSource::kInheritedDefault);
}

TEST(DisableIffResolution, RuleCNoInferenceEquivalentToFalse) {
  // §16.15 rule c): no clause and no enclosing default performs no inference,
  // equivalent to a 1'b0 disable condition.
  EXPECT_EQ(ResolveDisableConditionSource(false, false),
            DisableConditionSource::kNoneEquivalentToFalse);
}

TEST(DisableIffResolution, EffectIndependentOfDeclarationPosition) {
  // §16.15: a default disable iff governs assertions sharing its scope
  // regardless of whether the declaration appears before or after the
  // assertion, so both orderings are governed.
  EXPECT_TRUE(AssertionGovernedBySameScopeDefault(
      DeclarationPosition::kBeforeAssertion));
  EXPECT_TRUE(AssertionGovernedBySameScopeDefault(
      DeclarationPosition::kAfterAssertion));
}

}  // namespace
