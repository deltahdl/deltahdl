#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_specify_path_decl.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

TEST(PulseFiltering, PulseAtErrorLimitPropagates) {
  EXPECT_EQ(ClassifyPulse(7, 3, 7), PulseClassification::kPropagate);
}

TEST(PulseFiltering, PulseAtRejectLimitForcesXWhenErrorHigher) {
  EXPECT_EQ(ClassifyPulse(3, 3, 7), PulseClassification::kForceX);
}

TEST(PulseFiltering, PulseJustBelowErrorLimitForcesX) {
  EXPECT_EQ(ClassifyPulse(6, 3, 7), PulseClassification::kForceX);
}

TEST(PulseFiltering, PulseBelowRejectLimitIsRejected) {
  EXPECT_EQ(ClassifyPulse(2, 3, 7), PulseClassification::kReject);
}

TEST(PulseFiltering, ClassifierProducesOneOfThreeCategories) {
  PulseClassification a = ClassifyPulse(1, 3, 7);
  PulseClassification b = ClassifyPulse(5, 3, 7);
  PulseClassification c = ClassifyPulse(9, 3, 7);
  EXPECT_EQ(a, PulseClassification::kReject);
  EXPECT_EQ(b, PulseClassification::kForceX);
  EXPECT_EQ(c, PulseClassification::kPropagate);
}

TEST(PulseFilteringFromSource, DefaultLimitsMirrorParsedTransitionDelays) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = (7, 9);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 7u);
  ASSERT_EQ(pd.delays[1], 9u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 7u);
  EXPECT_EQ(pd.error_limit[0], 7u);
  EXPECT_EQ(pd.reject_limit[1], 9u);
  EXPECT_EQ(pd.error_limit[1], 9u);
}

TEST(PulseFilteringFromSource, NarrowPulseRejectedUnderDerivedDefaults) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = (7, 9);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse(2, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
  EXPECT_EQ(ClassifyPulse(7, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

TEST(PulseFilteringFromSource, TrailingEdgeDerivedLimitsGovern) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = (7, 9);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[1], pd.error_limit[1]),
            PulseClassification::kReject);
}

TEST(PulseFilteringFromSource, SpecparamDelayDrivesDefaultLimits) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y",
                             "    specparam d = 6;\n    (a => y) = d;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 6u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 6u);
  EXPECT_EQ(pd.error_limit[0], 6u);
  EXPECT_EQ(ClassifyPulse(3, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
}

TEST(PulseFilteringFromSource, MinTypMaxDelaySelectsDefaultLimit) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = 6:8:10;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 8u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 8u);
  EXPECT_EQ(pd.error_limit[0], 8u);
  EXPECT_EQ(ClassifyPulse(7, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

TEST(PulseFilteringFromSource, DefaultLimitsMirrorEverySlotFromSixDelays) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y",
                             "    (a => y) = (1, 2, 3, 4, 5, 6);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], pd.delays[i]) << "reject slot " << i;
    EXPECT_EQ(pd.error_limit[i], pd.delays[i]) << "error slot " << i;
  }
}

TEST(PulseFilteringFromSource, ClampedZeroDelayDisablesFiltering) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = -4;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 0u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
  EXPECT_EQ(ClassifyPulse(0, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
  EXPECT_EQ(ClassifyPulse(1, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

}  // namespace
