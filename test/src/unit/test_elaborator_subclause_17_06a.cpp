#include <gtest/gtest.h>

#include "elaborator/covergroup_in_checker.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(CovergroupInChecker, CovergroupInBodyIsLegalButNotInProceduralBlock) {
  EXPECT_TRUE(CheckerCovergroupPlacementIsLegal(
      CheckerCovergroupPlacement::kCheckerBody));
  EXPECT_FALSE(CheckerCovergroupPlacementIsLegal(
      CheckerCovergroupPlacement::kProceduralBlock));
}

TEST(CovergroupInChecker, CovergroupMayReferenceFormalsAndCheckerVariables) {
  EXPECT_TRUE(CheckerCovergroupMayReference(
      CheckerCovergroupReference::kCheckerFormalArgument));
  EXPECT_TRUE(CheckerCovergroupMayReference(
      CheckerCovergroupReference::kCheckerVariable));
  EXPECT_TRUE(CheckerCovergroupMayReference(
      CheckerCovergroupReference::kOtherVisibleVariable));
}

TEST(CovergroupInChecker, ConstActualForReferencedFormalIsAnError) {
  EXPECT_TRUE(CheckerCovergroupConstFormalIsError(true, true));
}

TEST(CovergroupInChecker, ConstActualIsLegalWhenFormalIsNotReferenced) {
  EXPECT_FALSE(CheckerCovergroupConstFormalIsError(false, true));
  EXPECT_FALSE(CheckerCovergroupConstFormalIsError(true, false));
  EXPECT_FALSE(CheckerCovergroupConstFormalIsError(false, false));
}

TEST(CovergroupInChecker, SampleMethodCallIsAPermittedTrigger) {
  EXPECT_TRUE(CheckerCovergroupTriggerIsPermitted(
      CheckerCovergroupTrigger::kClockingEvent));
  EXPECT_TRUE(CheckerCovergroupTriggerIsPermitted(
      CheckerCovergroupTrigger::kProceduralSampleCall));
}

TEST(CovergroupInChecker, CovergroupInCheckerBodyElaboratesAndIsCarried) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker my_check(logic clk, logic active);\n"
      "  bit active_d1 = 1'b0;\n"
      "  covergroup cg_active @(posedge clk);\n"
      "    cp_active : coverpoint active;\n"
      "    cp_active_d1 : coverpoint active_d1;\n"
      "  endgroup\n"
      "endchecker\n",
      f, "my_check");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];
  bool carries_covergroup = false;
  for (const ModuleItem* item : mod->let_decls) {
    if (item->kind == ModuleItemKind::kCovergroupDecl &&
        item->name == "cg_active") {
      carries_covergroup = true;
    }
  }
  EXPECT_TRUE(carries_covergroup);
}

TEST(CovergroupInChecker, InstanceInACheckerProcedureIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(logic a, logic clk);\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp: coverpoint a;\n"
      "  endgroup\n"
      "  cg cg_body = new();\n"
      "  always_ff @(posedge clk) begin\n"
      "    automatic cg cg_1 = new();\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "covergroup 'cg' cannot be instantiated in a "
                            "procedure of a checker",
                            7, "17.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CheckerCovergroupRules, AConstActualForACoveredFormalIsReported) {
  const char* const kReport =
      "the formal 'mode' of checker 'c', which a covergroup references, has a "
      "const actual";
  ElabFixture f;
  ElaborateSrc(
      "checker c(logic clk, logic [1:0] mode);\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp: coverpoint mode;\n"
      "    cq: coverpoint clk;\n"
      "    cr: cross cp, cq;\n"
      "  endgroup\n"
      "  cg cg_1 = new();\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic [1:0] x;\n"
      "  c u1(clk, const'(x));\n"
      "  c u2(clk, x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 12, "17.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 13, "17.6"));
}

}  // namespace
