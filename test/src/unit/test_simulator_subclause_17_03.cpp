#include <gtest/gtest.h>

#include "simulator/checker_instance_scheduling.h"

using namespace delta;

namespace {

TEST(CheckerInstanceScheduling, ProceduralVersusStaticClassification) {
  // §17.3: a checker instantiation in procedural code is a procedural checker
  // instance; one outside procedural code is a static checker instance.
  EXPECT_EQ(ClassifyCheckerInstance(/*instantiated_in_procedural_code=*/true),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(ClassifyCheckerInstance(/*instantiated_in_procedural_code=*/false),
            CheckerInstanceKind::kStatic);
}

TEST(CheckerInstanceScheduling, OnlyStaticAssertionsAreExemptFromEveryStep) {
  // §17.3: all contents other than static assertion statements exist during
  // every time step; static assertion statements are the exception.
  EXPECT_TRUE(CheckerContentExistsEveryTimeStep(
      /*is_static_assertion_statement=*/false));
  EXPECT_FALSE(CheckerContentExistsEveryTimeStep(
      /*is_static_assertion_statement=*/true));
}

TEST(CheckerInstanceScheduling, StaticConcurrentAssertionTreatment) {
  // §17.3: a static concurrent assertion is monitored directly in a static
  // checker and queued (pending procedural assertion queue) in a procedural
  // checker.
  EXPECT_EQ(TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, StaticDeferredAssertionTreatment) {
  // §17.3: a static deferred assertion is monitored on expression change in a
  // static checker and queued (pending deferred assertion report) in a
  // procedural checker.
  EXPECT_EQ(TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, NestedStaticCheckerFollowsTopLevelAncestor) {
  // §17.3: a static checker statically instantiated inside another checker has
  // its static assertions follow the top-level ancestor's instance kind; an
  // un-nested checker keeps its own kind.
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/true,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/true,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kStatic);
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/false,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kStatic);
  // Edge: when not nested, the instance's own kind is returned regardless of
  // any ancestor kind, so a procedural own kind is preserved.
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kProcedural,
                /*nested_inside_another_checker=*/false,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kProcedural);
}

}  // namespace
