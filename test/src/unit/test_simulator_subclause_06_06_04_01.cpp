#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_capacitive_pair.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

static Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval = uint64_t{0};
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
  ASSERT_EQ(la->charge_strength, Strength::kLarge);
  ASSERT_EQ(sm->charge_strength, Strength::kSmall);

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  sm->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);

  PropagateCharge(*la, *sm);

  EXPECT_EQ(sm->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(sm->charge_strength, Strength::kLarge);
  EXPECT_EQ(la->resolved->value.ToUint64() & 1u, 1u);
}

TEST(CapacitiveNetwork, EqualSizeDifferentValuesToXFromSource) {
  SimFixture f;
  auto [me1, me2] = MakeEqualSizeTriregs(f, 1, 0);
  ASSERT_NE(me1, nullptr);
  ASSERT_NE(me2, nullptr);

  PropagateCharge(*me1, *me2);

  EXPECT_EQ(me1->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(me1->resolved->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(me2->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(me2->resolved->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(me1->charge_strength, Strength::kMedium);
  EXPECT_EQ(me2->charge_strength, Strength::kMedium);
}

TEST(CapacitiveNetwork, NoSharingWhileOneNetDrivenFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) la;\n"
      "  trireg (small) sm;\n"
      "  assign sm = 1'b0;\n"
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
  ASSERT_FALSE(sm->InCapacitiveState());

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*la, *sm);

  EXPECT_EQ(la->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(sm->resolved->value.ToUint64() & 1u, 0u);
  EXPECT_EQ(sm->charge_strength, Strength::kSmall);
}

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
  ASSERT_EQ(sm->base_charge_strength, Strength::kSmall);

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  sm->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*la, *sm);
  EXPECT_EQ(sm->charge_strength, Strength::kLarge);

  DisconnectCharge(*sm);
  EXPECT_EQ(sm->charge_strength, Strength::kSmall);
}

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
  ASSERT_EQ(me->charge_strength, Strength::kMedium);
  ASSERT_EQ(sm->charge_strength, Strength::kSmall);

  me->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);
  sm->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);

  PropagateCharge(*me, *sm);

  EXPECT_EQ(sm->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(sm->charge_strength, Strength::kMedium);
}

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
  ASSERT_EQ(la->charge_strength, Strength::kLarge);
  ASSERT_EQ(me->charge_strength, Strength::kMedium);

  la->resolved->value = MakeLogic4VecVal(f.arena, 1, 0);
  me->resolved->value = MakeLogic4VecVal(f.arena, 1, 1);

  PropagateCharge(*la, *me);

  EXPECT_EQ(me->resolved->value.ToUint64() & 1u, 0u);
  EXPECT_EQ(me->charge_strength, Strength::kLarge);
}

TEST(CapacitiveNetwork, EqualSizeSameValueRetainedFromSource) {
  SimFixture f;
  auto [me1, me2] = MakeEqualSizeTriregs(f, 1, 1);
  ASSERT_NE(me1, nullptr);
  ASSERT_NE(me2, nullptr);

  PropagateCharge(*me1, *me2);

  EXPECT_EQ(me1->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(me2->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(me1->charge_strength, Strength::kMedium);
  EXPECT_EQ(me2->charge_strength, Strength::kMedium);
}

}  // namespace
