#include <gtest/gtest.h>

#include "elaborator/covergroup_in_checker.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CovergroupInChecker, CovergroupInBodyIsLegalButNotInProceduralBlock) {
  // §17.6: a covergroup declaration or instance is permitted within a checker,
  // as cg_active and cg_active_1 are in the my_check example, but it shall not
  // appear in any procedural block of the checker.
  EXPECT_TRUE(CheckerCovergroupPlacementIsLegal(
      CheckerCovergroupPlacement::kCheckerBody));
  EXPECT_FALSE(CheckerCovergroupPlacementIsLegal(
      CheckerCovergroupPlacement::kProceduralBlock));
}

TEST(CovergroupInChecker, CovergroupMayReferenceFormalsAndCheckerVariables) {
  // §17.6: a covergroup may reference any variable visible in its scope,
  // including checker formal arguments (such as active) and checker variables
  // (such as active_d1).
  EXPECT_TRUE(CheckerCovergroupMayReference(
      CheckerCovergroupReference::kCheckerFormalArgument));
  EXPECT_TRUE(CheckerCovergroupMayReference(
      CheckerCovergroupReference::kCheckerVariable));
  EXPECT_TRUE(CheckerCovergroupMayReference(
      CheckerCovergroupReference::kOtherVisibleVariable));
}

TEST(CovergroupInChecker, ConstActualForReferencedFormalIsAnError) {
  // §17.6: it shall be an error if a formal argument referenced by a covergroup
  // has a const actual argument.
  EXPECT_TRUE(CheckerCovergroupConstFormalIsError(
      /*formal_referenced_by_covergroup=*/true, /*actual_is_const=*/true));
}

TEST(CovergroupInChecker, ConstActualIsLegalWhenFormalIsNotReferenced) {
  // §17.6: the error is specific to a formal that a covergroup references; a
  // const actual is otherwise unobjectionable, and a referenced formal with a
  // non-const actual is fine.
  EXPECT_FALSE(CheckerCovergroupConstFormalIsError(
      /*formal_referenced_by_covergroup=*/false, /*actual_is_const=*/true));
  EXPECT_FALSE(CheckerCovergroupConstFormalIsError(
      /*formal_referenced_by_covergroup=*/true, /*actual_is_const=*/false));
  // Neither condition present: a formal that no covergroup references and whose
  // actual is not const is plainly fine.
  EXPECT_FALSE(CheckerCovergroupConstFormalIsError(
      /*formal_referenced_by_covergroup=*/false, /*actual_is_const=*/false));
}

TEST(CovergroupInChecker, SampleMethodCallIsAPermittedTrigger) {
  // §17.6: in addition to its clocking event, a covergroup in a checker may be
  // triggered by a procedural call to its sample() method, as op_test triggers
  // cg_op via cg_op_1.sample().
  EXPECT_TRUE(CheckerCovergroupTriggerIsPermitted(
      CheckerCovergroupTrigger::kClockingEvent));
  EXPECT_TRUE(CheckerCovergroupTriggerIsPermitted(
      CheckerCovergroupTrigger::kProceduralSampleCall));
}

// §17.6: one or more covergroup declarations are permitted within a checker,
// and a covergroup may reference any variable visible in its scope, including
// the checker's formal arguments and its checker variables. This drives the
// my_check shape from the clause — a covergroup built from real §19.3 syntax
// whose coverpoints read the checker formal `active` and the checker variable
// `active_d1` — through parse and elaboration and observes the real elaborator
// accepting it: the checker elaborates without error and its body carries the
// covergroup declaration.
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

}  // namespace
