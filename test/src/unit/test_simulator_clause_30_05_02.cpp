#include "fixture_simulator.h"
#include "fixture_specify_path_decl.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §30.5.2 derives the six x-transition delay slots (6-11) from the known-state
// slots (0-5) whenever the x transitions were not listed explicitly. Because
// the derivation's result depends on HOW the known-state slots were produced —
// the one/two/three/six-value forms of §30.5.1's Table 30-2 distribution each
// leave a different pattern in delays[0..5] — the rule is observed on a
// PathDelay built from real specify source through BuildPathDelayFromDecl
// (which runs the production ExpandTransitionDelays), not on a hand-assembled
// intermediate state.

// Claim A/B/C together, pinned by the Table 30-3 worked example
// (C => Q) = (5, 12, 17, 10, 6, 22). All six known-state delays are distinct,
// so every derived x slot lands on a unique value: this simultaneously fixes
// the to-x minimum rule, the from-x maximum rule, and each formula's operand
// choice. Six-value form built from real source.
TEST(SpecifyXTransitionSim, SixDelaysDeriveXSlotsLrmExample) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (5, 12, 17, 10, 6, 22);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 6u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[6], 5u);    // 0->x: min(t0z=17, t01=5)
  EXPECT_EQ(pd.delays[7], 10u);   // x->1: max(tz1=10, t01=5)
  EXPECT_EQ(pd.delays[8], 6u);    // 1->x: min(t1z=6, t10=12)
  EXPECT_EQ(pd.delays[9], 22u);   // x->0: max(tz0=22, t10=12)
  EXPECT_EQ(pd.delays[10], 17u);  // x->z: max(t1z=6, t0z=17)
  EXPECT_EQ(pd.delays[11], 10u);  // z->x: min(tz1=10, tz0=22)
}

// Input form: single value. Every known-state slot equals the typical delay, so
// each min/max collapses to that value and all six x slots inherit it.
TEST(SpecifyXTransitionSim, OneDelayDerivesEqualXSlots) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = 7;", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 1u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 6; i < 12; ++i) EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
}

// Input form: two values (rise, fall). The known-state slots split into a rise
// group {t01,t0z,tz1}=3 and a fall group {t10,t1z,tz0}=5, so the x slots are
// the min/max over those groups.
TEST(SpecifyXTransitionSim, TwoDelaysDeriveXSlotsFromRiseFall) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (3, 5);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 2u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[6], 3u);   // 0->x: min(t0z=3, t01=3)
  EXPECT_EQ(pd.delays[7], 3u);   // x->1: max(tz1=3, t01=3)
  EXPECT_EQ(pd.delays[8], 5u);   // 1->x: min(t1z=5, t10=5)
  EXPECT_EQ(pd.delays[9], 5u);   // x->0: max(tz0=5, t10=5)
  EXPECT_EQ(pd.delays[10], 5u);  // x->z: max(t1z=5, t0z=3)
  EXPECT_EQ(pd.delays[11], 3u);  // z->x: min(tz1=3, tz0=5)
}

// Input form: three values (rise, fall, z). The z column feeds t0z and t1z, so
// the derived x slots differ from the two-value case at the z-touching
// formulas.
TEST(SpecifyXTransitionSim, ThreeDelaysDeriveXSlots) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (2, 4, 6);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 3u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  // known-state slots: t01=2 t10=4 t0z=6 tz1=2 t1z=6 tz0=4
  EXPECT_EQ(pd.delays[6], 2u);   // 0->x: min(t0z=6, t01=2)
  EXPECT_EQ(pd.delays[7], 2u);   // x->1: max(tz1=2, t01=2)
  EXPECT_EQ(pd.delays[8], 4u);   // 1->x: min(t1z=6, t10=4)
  EXPECT_EQ(pd.delays[9], 4u);   // x->0: max(tz0=4, t10=4)
  EXPECT_EQ(pd.delays[10], 6u);  // x->z: max(t1z=6, t0z=6)
  EXPECT_EQ(pd.delays[11], 2u);  // z->x: min(tz1=2, tz0=4)
}

// Negative form: the opening conditional applies ONLY when the x transitions
// are implicit. A full twelve-value list explicitly specifies the x slots, so
// the derivation must leave them exactly as written. Built from real source.
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

// Operand data-type form: the six known-state delays are specparams (§30.5)
// rather than literals. Same Table 30-3 numbers as the literal example,
// resolved only after elaborate+lower seeds the specparams, so the x-slot
// derivation is observed on genuinely computed operands.
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
  EXPECT_EQ(pd.delays[6], 5u);    // 0->x: min(17, 5)
  EXPECT_EQ(pd.delays[7], 10u);   // x->1: max(10, 5)
  EXPECT_EQ(pd.delays[8], 6u);    // 1->x: min(6, 12)
  EXPECT_EQ(pd.delays[9], 22u);   // x->0: max(22, 12)
  EXPECT_EQ(pd.delays[10], 17u);  // x->z: max(6, 17)
  EXPECT_EQ(pd.delays[11], 10u);  // z->x: min(10, 22)
}

}  // namespace
