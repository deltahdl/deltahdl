#include <gtest/gtest.h>

#include "elaborator/disable_iff_resolution.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.15: more than one default disable iff declaration within the same module
// declaration shall be an error. Built from real source and driven through
// parse + elaborate so the production check (Elaborator::
// ValidateDuplicateDefaultDisableIff) is what reports the error.
TEST(DisableIffResolution, DuplicateInModuleIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit clk, rst1, rst2;\n"
      "  default disable iff rst1;\n"
      "  default disable iff rst2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §16.15: a single default disable iff is legal -- the accepting path opposite
// the duplicate error, so the check does not flag a lone declaration.
TEST(DisableIffResolution, SingleInModuleIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit clk, rst1;\n"
      "  default disable iff rst1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.15: the error rule applies to an interface declaration too -- the clause
// enumerates module, interface, and program as legal declaration scopes. The
// interface is instantiated so its body is elaborated.
TEST(DisableIffResolution, DuplicateInInterfaceIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  bit rst1, rst2;\n"
      "  default disable iff rst1;\n"
      "  default disable iff rst2;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §16.15: and to a program declaration. The program is named as the explicit
// top so its body is actually elaborated.
TEST(DisableIffResolution, DuplicateInProgramIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p(input bit rst1, input bit rst2);\n"
      "  default disable iff rst1;\n"
      "  default disable iff rst2;\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(f.has_errors);
}

// §16.15: the error is per scope. A default disable iff in a module and another
// in a textually nested module declaration are in two separate scopes, so
// neither is a duplicate of the other and elaboration is clean.
TEST(DisableIffResolution, SeparateScopesAreNotDuplicates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module outer;\n"
      "  bit rst1;\n"
      "  default disable iff rst1;\n"
      "  module inner;\n"
      "    bit rst2;\n"
      "    default disable iff rst2;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "outer");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.15: the uniqueness rule also names the generate block as a scope. Two
// default disable iff declarations in the same generate block are an error.
// Built from real source and elaborated so the production recursion into the
// generate block observes the rule.
TEST(DisableIffResolution, DuplicateInGenerateBlockIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit rst1, rst2;\n"
      "  if (1) begin\n"
      "    default disable iff rst1;\n"
      "    default disable iff rst2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §16.15: each generate block is a separate scope, so one default disable iff
// in each of two distinct generate blocks is not a duplicate and elaborates
// cleanly -- the accepting contrast to the generate-block error above.
TEST(DisableIffResolution, SeparateGenerateBlocksAreNotDuplicates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit rst1, rst2;\n"
      "  if (1) begin\n"
      "    default disable iff rst1;\n"
      "  end\n"
      "  if (1) begin\n"
      "    default disable iff rst2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DisableIffResolution, DeclarationSitesAreLegal) {
  // §16.15: a default disable iff may be declared within a module, interface,
  // or program declaration, or within a generate block.
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kModule));
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kInterface));
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kProgram));
  EXPECT_TRUE(
      DefaultDisableIffAllowedInScope(DisableIffScopeKind::kGenerateBlock));
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
