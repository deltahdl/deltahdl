#include <gtest/gtest.h>

#include "elaborator/covergroup_in_checker.h"

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

}  // namespace
