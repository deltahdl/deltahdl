#include <gtest/gtest.h>

#include "elaborator/disable_iff_resolution.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one default disable iff declaration is allowed per", 4, "16.15"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one default disable iff declaration is allowed per", 4, "16.15"));
}

TEST(DisableIffResolution, DuplicateInProgramIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p(input bit rst1, input bit rst2);\n"
      "  default disable iff rst1;\n"
      "  default disable iff rst2;\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one default disable iff declaration is allowed per", 3, "16.15"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one default disable iff declaration is allowed per", 5, "16.15"));
}

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
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kModule));
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kInterface));
  EXPECT_TRUE(DefaultDisableIffAllowedInScope(DisableIffScopeKind::kProgram));
  EXPECT_TRUE(
      DefaultDisableIffAllowedInScope(DisableIffScopeKind::kGenerateBlock));
}

TEST(DisableIffResolution, ExtendsIntoNestedDeclarationsAndGenerateBlocks) {
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
  EXPECT_FALSE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kModuleInstance));
  EXPECT_FALSE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kInterfaceInstance));
  EXPECT_FALSE(
      DefaultDisablePropagatesAcross(ScopeBoundaryKind::kProgramInstance));
}

TEST(DisableIffResolution, NestedDeclarationOverridesOuter) {
  EXPECT_TRUE(NestedDefaultOverridesOuter(true));
  EXPECT_FALSE(NestedDefaultOverridesOuter(false));
}

TEST(DisableIffResolution, SignalsResolveInDeclaringScope) {
  EXPECT_EQ(DefaultDisableSignalResolutionScope(),
            DisableSignalScope::kDeclaringScope);
}

TEST(DisableIffResolution, RuleAExplicitClauseWins) {
  EXPECT_EQ(ResolveDisableConditionSource(true, true),
            DisableConditionSource::kExplicitClause);
  EXPECT_EQ(ResolveDisableConditionSource(true, false),
            DisableConditionSource::kExplicitClause);
}

TEST(DisableIffResolution, RuleBInheritsDefaultInScope) {
  EXPECT_EQ(ResolveDisableConditionSource(false, true),
            DisableConditionSource::kInheritedDefault);
}

TEST(DisableIffResolution, RuleCNoInferenceEquivalentToFalse) {
  EXPECT_EQ(ResolveDisableConditionSource(false, false),
            DisableConditionSource::kNoneEquivalentToFalse);
}

TEST(DisableIffResolution, EffectIndependentOfDeclarationPosition) {
  EXPECT_TRUE(AssertionGovernedBySameScopeDefault(
      DeclarationPosition::kBeforeAssertion));
  EXPECT_TRUE(AssertionGovernedBySameScopeDefault(
      DeclarationPosition::kAfterAssertion));
}

TEST(DisableIffResolution, DuplicateDefaultDisableIffNames16_15) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, rst1, rst2;\n"
      "  default disable iff rst1;\n"
      "  default disable iff rst2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one default disable iff declaration is allowed", 4, "16.15"));
}

}  // namespace
