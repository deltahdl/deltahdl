#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "fixture_specify_path_decl.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

TEST(SpecifyXTransitionSim, SixDelaysDeriveXSlotsLrmExample) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (5, 12, 17, 10, 6, 22);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 6u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[6], 5u);
  EXPECT_EQ(pd.delays[7], 10u);
  EXPECT_EQ(pd.delays[8], 6u);
  EXPECT_EQ(pd.delays[9], 22u);
  EXPECT_EQ(pd.delays[10], 17u);
  EXPECT_EQ(pd.delays[11], 10u);
}

TEST(SpecifyXTransitionSim, OneDelayDerivesEqualXSlots) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = 7;", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 1u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 6; i < 12; ++i) EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
}

TEST(SpecifyXTransitionSim, TwoDelaysDeriveXSlotsFromRiseFall) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (3, 5);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 2u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[6], 3u);
  EXPECT_EQ(pd.delays[7], 3u);
  EXPECT_EQ(pd.delays[8], 5u);
  EXPECT_EQ(pd.delays[9], 5u);
  EXPECT_EQ(pd.delays[10], 5u);
  EXPECT_EQ(pd.delays[11], 3u);
}

TEST(SpecifyXTransitionSim, ThreeDelaysDeriveXSlots) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (2, 4, 6);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 3u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[6], 2u);
  EXPECT_EQ(pd.delays[7], 2u);
  EXPECT_EQ(pd.delays[8], 4u);
  EXPECT_EQ(pd.delays[9], 4u);
  EXPECT_EQ(pd.delays[10], 6u);
  EXPECT_EQ(pd.delays[11], 2u);
}

TEST(SpecifyXTransitionSim, TwelveDelaysPreserveExplicitXSlots) {
  SimFixture f;
  const auto* decl = FirstPathDecl(
      "    (a => b) = (20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 12u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], static_cast<uint64_t>(20 + i)) << "slot " << i;
  }
}

TEST(SpecifyXTransitionSim, SpecparamDelaysDeriveXSlots) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output b",
                             "    specparam t01 = 5, t10 = 12, t0z = 17, tz1 = "
                             "10, t1z = 6, tz0 = 22;\n"
                             "    (a => b) = (t01, t10, t0z, tz1, t1z, tz0);",
                             f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_EQ(c.decl->delays.size(), 6u);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[6], 5u);
  EXPECT_EQ(pd.delays[7], 10u);
  EXPECT_EQ(pd.delays[8], 6u);
  EXPECT_EQ(pd.delays[9], 22u);
  EXPECT_EQ(pd.delays[10], 17u);
  EXPECT_EQ(pd.delays[11], 10u);
}

}  // namespace
