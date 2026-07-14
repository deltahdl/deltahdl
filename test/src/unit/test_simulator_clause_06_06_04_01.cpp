#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

static Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval =
        uint64_t{0};  // canonical Convention A: z = (aval=0, bval=1)
    vec.words[w].bval = ~uint64_t{0};
  }
  return vec;
}

static Net MakeTriregNet(Arena& arena, Variable*& var, Strength strength,
                         uint32_t width, uint64_t initial_val) {
  var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, width, initial_val);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.charge_strength = strength;
  net.base_charge_strength = strength;
  net.drivers.push_back(MakeAllZ(arena, width));
  return net;
}

namespace {

TEST(CapacitiveNetwork, SmallerFirstArgStillOverridden) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kSmall, 8, 0);
  Net b = MakeTriregNet(arena, var_b, Strength::kLarge, 8, 1);

  PropagateCharge(a, b);
  EXPECT_EQ(var_a->value.ToUint64(), 1u);
  EXPECT_EQ(var_b->value.ToUint64(), 1u);
}

TEST(CapacitiveNetwork, MultiWordVectorPropagation) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;

  Net a = MakeTriregNet(arena, var_a, Strength::kLarge, 128, 0xDEAD);
  Net b = MakeTriregNet(arena, var_b, Strength::kSmall, 128, 0xBEEF);

  PropagateCharge(a, b);
  EXPECT_EQ(var_b->value.ToUint64(), 0xDEADu);
  EXPECT_EQ(var_a->value.ToUint64(), 0xDEADu);
}

// §6.6.4.1 edge: propagation happens only while BOTH trireg nets are in the
// capacitive state. OnlyWhenBothCapacitive drives the second net; this drives
// the first net instead, so the other operand of the capacitive-state guard is
// observed to block propagation. The driven net keeps its value and the
// capacitive net is left unchanged.
TEST(CapacitiveNetwork, NoPropagationWhenFirstNetDriven) {
  Arena arena;
  auto* var_a = arena.Create<Variable>();
  var_a->value = MakeLogic4VecVal(arena, 8, 1);
  Net a;
  a.type = NetType::kTrireg;
  a.resolved = var_a;
  a.charge_strength = Strength::kSmall;
  a.base_charge_strength = Strength::kSmall;
  a.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));

  Variable* var_b = nullptr;
  Net b = MakeTriregNet(arena, var_b, Strength::kLarge, 8, 0);

  PropagateCharge(a, b);

  EXPECT_EQ(var_a->value.ToUint64(), 1u);
  EXPECT_EQ(var_b->value.ToUint64(), 0u);
}

// The tests above hand-build the trireg Nets so PropagateCharge can be
// exercised in isolation. The rule, however, turns on an input whose production
// matters: the per-net charge size that decides which net is the "larger" one
// is the declared capacitive strength (§6.3.2.1), not an arbitrary enum. The
// tests below build that input from real source -- two trireg nets declared
// with different sizes -- elaborate and lower them, and apply §6.6.4.1's charge
// rule to the real Nets, so the size ordering that picks the winner is the
// declared (large)/(medium)/(small) carried through the elaborator into the
// net's charge_strength. The nets are left undriven, which is the capacitive
// state (no driver is the all-z case, §6.6.4), so InCapacitiveState() -- the
// guard PropagateCharge consumes -- is satisfied by the real lowered net rather
// than a synthesised driver list. A capacitive network forms through a §28
// bidirectional switch, which has no runtime hookup here, so the rule is
// invoked directly on the two real capacitive-state nets; only the held logic
// value is seeded (the value a trireg happens to be storing is ordinary runtime
// state).

// §6.6.4.1: charge propagates from the larger trireg net to the smaller one;
// the smaller adopts both the value and the charge strength of the larger. The
// size ordering that makes (large) win over (small) is read from the real
// declarations rather than assigned by hand.
TEST(CapacitiveNetwork, LargerOverridesSmallerFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) la;\n"
      "  trireg (small) sm;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* la = f.ctx.FindNet("la");
  auto* sm = f.ctx.FindNet("sm");
  ASSERT_NE(la, nullptr);
  ASSERT_NE(sm, nullptr);
  ASSERT_TRUE(la->InCapacitiveState());
  ASSERT_TRUE(sm->InCapacitiveState());
  ASSERT_EQ(la->charge_strength, Strength::kLarge);  // from real (large)
  ASSERT_EQ(sm->charge_strength, Strength::kSmall);  // from real (small)

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);  // large net holds 1
  sm->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);  // small net holds 0

  PropagateCharge(*la, *sm);

  EXPECT_EQ(sm->resolved->value.ToUint64() & 1u, 1u);  // adopts larger's 1
  EXPECT_EQ(sm->charge_strength, Strength::kLarge);    // adopts larger strength
  EXPECT_EQ(la->resolved->value.ToUint64() & 1u, 1u);  // larger unchanged
}

// §6.6.4.1: two trireg nets of equal size holding different stored values both
// change to x. The equal-size condition is the two real (medium) declarations.
TEST(CapacitiveNetwork, EqualSizeDifferentValuesToXFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (medium) me1;\n"
      "  trireg (medium) me2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* me1 = f.ctx.FindNet("me1");
  auto* me2 = f.ctx.FindNet("me2");
  ASSERT_NE(me1, nullptr);
  ASSERT_NE(me2, nullptr);
  ASSERT_TRUE(me1->InCapacitiveState());
  ASSERT_TRUE(me2->InCapacitiveState());
  ASSERT_EQ(me1->charge_strength, me2->charge_strength);  // both (medium)

  me1->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  me2->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);

  PropagateCharge(*me1, *me2);

  // x = (aval=1, bval=1) in Convention A.
  EXPECT_EQ(me1->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(me1->resolved->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(me2->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(me2->resolved->value.words[0].bval & 1u, 1u);
  // Only the logic value changes: an equal-size conflict leaves each net's
  // charge strength alone (no larger side to adopt from).
  EXPECT_EQ(me1->charge_strength, Strength::kMedium);
  EXPECT_EQ(me2->charge_strength, Strength::kMedium);
}

// §6.6.4.1: charge sharing occurs only while both trireg nets are in the
// capacitive state. The small net is kept actively driven by a real continuous
// assignment (§28), so it is not capacitive when the large net is; the rule
// must leave both nets untouched. The driven-vs-capacitive distinction comes
// from real source -- one net has a live driver, the other does not.
TEST(CapacitiveNetwork, NoSharingWhileOneNetDrivenFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) la;\n"
      "  trireg (small) sm;\n"
      "  assign sm = 1'b0;\n"  // sm permanently driven -> not capacitive
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* la = f.ctx.FindNet("la");
  auto* sm = f.ctx.FindNet("sm");
  ASSERT_NE(la, nullptr);
  ASSERT_NE(sm, nullptr);
  ASSERT_TRUE(la->InCapacitiveState());
  ASSERT_FALSE(sm->InCapacitiveState());  // driven by assign sm = 1'b0

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*la, *sm);

  EXPECT_EQ(la->resolved->value.ToUint64() & 1u, 1u);  // large net unchanged
  EXPECT_EQ(sm->resolved->value.ToUint64() & 1u, 0u);  // driven net unchanged
  EXPECT_EQ(sm->charge_strength, Strength::kSmall);    // no strength adoption
}

// §6.6.4.1 (Figure 6-3 charge sharing): once a smaller trireg net no longer
// shares the larger net's charge, it reverts to its own declared charge
// strength. The small net first adopts the large strength through sharing, then
// DisconnectCharge restores the base strength -- which must be the declared
// (small) size carried through from source, not a hand-set base.
TEST(CapacitiveNetwork, DisconnectRestoresDeclaredStrengthFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) la;\n"
      "  trireg (small) sm;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* la = f.ctx.FindNet("la");
  auto* sm = f.ctx.FindNet("sm");
  ASSERT_NE(la, nullptr);
  ASSERT_NE(sm, nullptr);
  ASSERT_EQ(sm->base_charge_strength, Strength::kSmall);  // from real (small)

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  sm->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*la, *sm);
  EXPECT_EQ(sm->charge_strength, Strength::kLarge);  // shares large charge

  DisconnectCharge(*sm);
  EXPECT_EQ(sm->charge_strength, Strength::kSmall);  // reverts to declared size
}

// §6.6.4.1: the size comparison is not confined to the large/small extremes --
// an intermediate (medium) net acts as the larger side against a (small) net.
// Both sizes are read from real declarations, so the ordering that picks the
// winner is medium > small as carried through the elaborator, not a hand-set
// enum. The small net adopts the medium net's value and charge strength.
TEST(CapacitiveNetwork, MediumOverridesSmallFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (medium) me;\n"
      "  trireg (small) sm;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* me = f.ctx.FindNet("me");
  auto* sm = f.ctx.FindNet("sm");
  ASSERT_NE(me, nullptr);
  ASSERT_NE(sm, nullptr);
  ASSERT_TRUE(me->InCapacitiveState());
  ASSERT_TRUE(sm->InCapacitiveState());
  ASSERT_EQ(me->charge_strength, Strength::kMedium);  // from real (medium)
  ASSERT_EQ(sm->charge_strength, Strength::kSmall);   // from real (small)

  me->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  sm->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);

  PropagateCharge(*me, *sm);

  EXPECT_EQ(sm->resolved->value.ToUint64() & 1u, 1u);  // adopts medium's 1
  EXPECT_EQ(sm->charge_strength, Strength::kMedium);   // adopts medium strength
}

// §6.6.4.1: the other intermediate ordering -- a (large) net acts as the larger
// side against a (medium) net -- again with both sizes taken from real
// declarations. This completes the small < medium < large chain end-to-end.
TEST(CapacitiveNetwork, LargeOverridesMediumFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) la;\n"
      "  trireg (medium) me;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* la = f.ctx.FindNet("la");
  auto* me = f.ctx.FindNet("me");
  ASSERT_NE(la, nullptr);
  ASSERT_NE(me, nullptr);
  ASSERT_TRUE(la->InCapacitiveState());
  ASSERT_TRUE(me->InCapacitiveState());
  ASSERT_EQ(la->charge_strength, Strength::kLarge);   // from real (large)
  ASSERT_EQ(me->charge_strength, Strength::kMedium);  // from real (medium)

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);
  me->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*la, *me);

  EXPECT_EQ(me->resolved->value.ToUint64() & 1u, 0u);  // adopts large's 0
  EXPECT_EQ(me->charge_strength, Strength::kLarge);    // adopts large strength
}

// §6.6.4.1 (non-firing path): two equal-size trireg nets holding the SAME value
// are left unchanged -- there is no conflict, so neither the value nor the
// charge strength moves. The equal-size condition is the two real (medium)
// declarations, the complement of the equal-size different-value conflict that
// resolves to x above.
TEST(CapacitiveNetwork, EqualSizeSameValueRetainedFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (medium) me1;\n"
      "  trireg (medium) me2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* me1 = f.ctx.FindNet("me1");
  auto* me2 = f.ctx.FindNet("me2");
  ASSERT_NE(me1, nullptr);
  ASSERT_NE(me2, nullptr);
  ASSERT_TRUE(me1->InCapacitiveState());
  ASSERT_TRUE(me2->InCapacitiveState());
  ASSERT_EQ(me1->charge_strength, me2->charge_strength);  // both (medium)

  me1->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  me2->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*me1, *me2);

  EXPECT_EQ(me1->resolved->value.ToUint64() & 1u, 1u);  // retained, no x
  EXPECT_EQ(me2->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(me1->charge_strength, Strength::kMedium);
  EXPECT_EQ(me2->charge_strength, Strength::kMedium);
}

}  // namespace
