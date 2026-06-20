#include <gtest/gtest.h>

#include "elaborator/checker_instantiation.h"

using namespace delta;

namespace {

TEST(CheckerInstantiation, AllowedInConcurrentAssertionContext) {
  // §17.3: a checker may be instantiated wherever a concurrent assertion may
  // appear.
  EXPECT_TRUE(CheckerInstantiationSiteIsLegal(
      CheckerInstantiationSite::kConcurrentAssertionContext));
}

TEST(CheckerInstantiation, IllegalInForkJoinBlocks) {
  // §17.3: it is illegal to instantiate checkers in fork-join, fork-join_any,
  // or fork-join_none blocks.
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoin));
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoinAny));
  EXPECT_FALSE(
      CheckerInstantiationSiteIsLegal(CheckerInstantiationSite::kForkJoinNone));
}

TEST(CheckerInstantiation, IllegalInProcedureOfAnotherChecker) {
  // §17.3: it is illegal to instantiate a checker in a procedure of another
  // checker.
  EXPECT_FALSE(CheckerInstantiationSiteIsLegal(
      CheckerInstantiationSite::kProcedureOfAnotherChecker));
}

TEST(CheckerInstantiation, OutputActualArgMustBeVariableOrNetLvalue) {
  // §17.3: each checker actual output argument shall be a variable_lvalue or a
  // net_lvalue.
  EXPECT_TRUE(
      CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kVariableLvalue));
  EXPECT_TRUE(
      CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kNetLvalue));
  EXPECT_FALSE(CheckerOutputActualArgIsLegal(CheckerOutputActualArg::kOther));
}

TEST(CheckerInstantiation, AllFourPortConnectionStylesSupported) {
  // §17.3: formal arguments may be connected like module ports, using
  // positional, fully explicit named, implicit named, and wildcard styles.
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kPositional));
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kNamedExplicit));
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kNamedImplicit));
  EXPECT_TRUE(IsSupportedCheckerPortConnectionStyle(
      CheckerPortConnectionStyle::kWildcard));
}

TEST(CheckerInstantiation, DollarFormalReferencePermittedUses) {
  // §17.3: a reference of a formal bound to `$` is legal only as a cycle-delay
  // range upper bound, an actual to a sequence/property/checker instance, or a
  // nested checker default argument.
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kCycleDelayRangeUpperBound));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kSequenceInstanceActual));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kPropertyInstanceActual));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kCheckerInstanceActual));
  EXPECT_TRUE(DollarFormalReferenceIsLegal(
      DollarFormalReferenceUse::kNestedCheckerDefaultArg));
  EXPECT_FALSE(DollarFormalReferenceIsLegal(DollarFormalReferenceUse::kOther));
}

TEST(CheckerInstantiation, DollarActualRequiresUntypedFormalAndPermittedRefs) {
  // §17.3: when `$` is an actual input argument, the corresponding formal shall
  // be untyped and each of its references shall be a permitted use.
  EXPECT_TRUE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/true,
                                  /*all_formal_references_permitted=*/true));
  EXPECT_FALSE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/false,
                                  /*all_formal_references_permitted=*/true));
  EXPECT_FALSE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/true,
                                  /*all_formal_references_permitted=*/false));
  EXPECT_FALSE(
      DollarActualArgumentIsLegal(/*formal_is_untyped=*/false,
                                  /*all_formal_references_permitted=*/false));
}

TEST(CheckerInstantiation, ConstCastOrAutomaticActualRestrictsFormalUsage) {
  // §17.3: an actual input argument carrying a const cast or automatic value
  // from procedural code forbids using the formal in a continuous assignment or
  // in the checker's procedural code.
  EXPECT_TRUE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/false,
      /*formal_used_in_continuous_assignment=*/true,
      /*formal_used_in_procedural_code=*/true));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/true,
      /*formal_used_in_procedural_code=*/false));
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/false,
      /*formal_used_in_procedural_code=*/true));
  EXPECT_TRUE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/false,
      /*formal_used_in_procedural_code=*/false));
  // Edge: both forbidden usages present at once is still rejected.
  EXPECT_FALSE(ConstCastOrAutomaticActualFormalUsageIsLegal(
      /*actual_has_const_cast_or_automatic_value=*/true,
      /*formal_used_in_continuous_assignment=*/true,
      /*formal_used_in_procedural_code=*/true));
}

}  // namespace
