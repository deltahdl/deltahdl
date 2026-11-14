#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>

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

struct DuplicatedDefault {
  const char* place;
  const char* src;
  uint32_t line;
};

constexpr const char* kDuplicateMessage =
    "only one default disable iff declaration is allowed per";

void ExpectEachDuplicateReported(const DuplicatedDefault* cases, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    ElabFixture f;
    ElaborateSrc(cases[i].src, f, "m");
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDuplicateMessage,
                              cases[i].line, "16.15"))
        << cases[i].place;
  }
}

void ExpectEachAccepted(std::initializer_list<const char*> sources) {
  for (const char* src : sources) {
    ElabFixture f;
    auto* design = ElaborateSrc(src, f, "m");
    EXPECT_NE(design, nullptr) << src;
    EXPECT_FALSE(f.has_errors) << src;
  }
}

TEST(DisableIffResolution, DuplicatesInEachGenerateFormAreReported) {
  const DuplicatedDefault kCases[] = {
      {"loop generate block",
       "module m;\n  bit r1, r2;\n  for (genvar i = 0; i < 2; i++) begin : g\n"
       "    default disable iff r1;\n    default disable iff r2;\n  end\n"
       "endmodule\n",
       5},
      {"case generate item",
       "module m;\n  bit r1, r2;\n  case (1)\n    1: begin : g\n"
       "      default disable iff r1;\n      default disable iff r2;\n"
       "    end\n  endcase\nendmodule\n",
       6},
      {"else branch",
       "module m;\n  bit r1, r2;\n  if (0) begin : g0\n  end else begin : g1\n"
       "    default disable iff r1;\n    default disable iff r2;\n  end\n"
       "endmodule\n",
       6},
      {"unselected branch",
       "module m;\n  bit r1, r2;\n  if (0) begin : g0\n"
       "    default disable iff r1;\n    default disable iff r2;\n  end\n"
       "endmodule\n",
       5},
      {"nested generate block",
       "module m;\n  bit r1, r2;\n  if (1) begin : g\n    if (1) begin : h\n"
       "      default disable iff r1;\n      default disable iff r2;\n"
       "    end\n  end\nendmodule\n",
       6},
  };
  ExpectEachDuplicateReported(kCases, sizeof(kCases) / sizeof(kCases[0]));
}

TEST(DisableIffResolution, OnePerGenerateFormIsAccepted) {
  ExpectEachAccepted(
      {"module m;\n  bit r1;\n  for (genvar i = 0; i < 2; i++) begin : g\n"
       "    default disable iff r1;\n  end\nendmodule\n",
       "module m;\n  bit r1;\n  case (1)\n    1: begin : g\n"
       "      default disable iff r1;\n    end\n  endcase\nendmodule\n",
       "module m;\n  bit r1, r2;\n  if (1) begin : g\n"
       "    default disable iff r1;\n    if (1) begin : h\n"
       "      default disable iff r2;\n    end\n  end\nendmodule\n",
       "module m;\n  bit r1;\n  generate\n    default disable iff r1;\n"
       "  endgenerate\nendmodule\n",
       "module m;\n  bit r1, r2;\n  default disable iff r1;\n"
       "  if (1) begin : g\n    default disable iff r2;\n  end\nendmodule\n"});
}

TEST(DisableIffResolution, DuplicatesInAModuleOrANestedDeclarationAreReported) {
  const DuplicatedDefault kCases[] = {
      {"module with items between",
       "module m;\n  bit clk, a, r1, r2;\n  default disable iff r1;\n"
       "  assert property (@(posedge clk) a);\n  default disable iff r2;\n"
       "endmodule\n",
       5},
      {"module and generate region",
       "module m;\n  bit r1, r2;\n  default disable iff r1;\n  generate\n"
       "    default disable iff r2;\n  endgenerate\nendmodule\n",
       5},
      {"nested module",
       "module m;\n  module n;\n    bit r1, r2;\n"
       "    default disable iff r1;\n    default disable iff r2;\n"
       "  endmodule\nendmodule\n",
       5},
      {"nested program",
       "module m;\n  program n;\n    bit r1, r2;\n"
       "    default disable iff r1;\n    default disable iff r2;\n"
       "  endprogram\nendmodule\n",
       5},
  };
  ExpectEachDuplicateReported(kCases, sizeof(kCases) / sizeof(kCases[0]));
}

TEST(DisableIffResolution,
     DISABLED_DuplicatesInAnUninstantiatedInterfaceAreReported) {
  const DuplicatedDefault kCases[] = {
      {"nested interface",
       "module m;\n  interface i;\n    bit r1, r2;\n"
       "    default disable iff r1;\n    default disable iff r2;\n"
       "  endinterface\nendmodule\n",
       5},
      {"top-level interface",
       "interface i;\n  bit r1, r2;\n  default disable iff r1;\n"
       "  default disable iff r2;\nendinterface\nmodule m;\nendmodule\n",
       4},
  };
  ExpectEachDuplicateReported(kCases, sizeof(kCases) / sizeof(kCases[0]));
}

TEST(DisableIffResolution, OnePerInterfaceProgramOrNestedDeclarationAccepted) {
  ExpectEachAccepted(
      {"interface i;\n  bit r1;\n  default disable iff r1;\nendinterface\n"
       "program p;\n  bit r1;\n  default disable iff r1;\nendprogram\n"
       "module m;\n  i u_i();\n  p u_p();\nendmodule\n",
       "module m;\n  bit r1;\n  default disable iff r1;\n  interface ni;\n"
       "    bit r2;\n    default disable iff r2;\n  endinterface\n"
       "  program np;\n    bit r2;\n    default disable iff r2;\n"
       "  endprogram\n  ni u_ni();\n  np u_np();\nendmodule\n"});
}

}  // namespace
