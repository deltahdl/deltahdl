#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static Logic4Vec MakeZVec(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval = ~uint64_t{0};
    v.words[w].bval = ~uint64_t{0};
  }
  return v;
}

static bool IsAllZ(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].aval != ~uint64_t{0}) return false;
    if (v.words[w].bval != ~uint64_t{0}) return false;
  }
  return true;
}

static Logic4Vec MakeXVec(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval = 0;
    v.words[w].bval = ~uint64_t{0};
  }
  return v;
}

// §6.6.4: driven state. When at least one driver carries 0/1/x, the resolved
// driver value propagates into the trireg and becomes its driven value.
TEST(TriregResolution, TriregDrivenNormally) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TriregResolution, MultipleDrivenDriversResolve) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

// §6.6.4 edge: x is listed as a driving value, so an all-x driver places the
// trireg in the driven state -- the unknown value propagates as the driven
// value and is not held as stored charge.
TEST(TriregResolution, UnknownDriverPutsNetInDrivenState) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0x5A);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeXVec(arena, 8));
  net.Resolve(arena);

  EXPECT_FALSE(net.InCapacitiveState());
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFFu, 0xFFu);
}

// §6.6.4 edge: the driven state needs only one driver carrying a non-z value.
// With one high-impedance driver and one driving driver, the net stays driven
// and follows the driving driver; it does not enter the capacitive state.
TEST(TriregResolution, OneActiveDriverAmongHighZKeepsNetDriven) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeZVec(arena, 8));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x55));
  net.Resolve(arena);

  EXPECT_FALSE(net.InCapacitiveState());
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

// §6.6.4: capacitive state. When every driver is at the high-impedance value,
// the trireg retains its last driven value -- the z does not propagate into the
// net. This is also what makes a trireg a value-storing net.
TEST(TriregResolution, CapacitiveStateRetainsLastDrivenValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x7E));
  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64(), 0x7Eu);
  EXPECT_FALSE(net.InCapacitiveState());

  // All drivers go to z: the high-impedance value must not propagate; the last
  // driven value is held instead.
  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_TRUE(net.InCapacitiveState());
  EXPECT_EQ(var->value.ToUint64(), 0x7Eu);
  EXPECT_FALSE(IsAllZ(var->value));
}

// §6.6.4: leaving the capacitive state by driving the net again replaces the
// stored charge with the new driven value.
TEST(TriregResolution, ReturningToDrivenStateReplacesStoredValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x11));
  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64(), 0x11u);

  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  ASSERT_TRUE(net.InCapacitiveState());
  ASSERT_EQ(var->value.ToUint64(), 0x11u);

  net.drivers[0] = MakeLogic4VecVal(arena, 8, 0x22);
  net.Resolve(arena);
  EXPECT_FALSE(net.InCapacitiveState());
  EXPECT_EQ(var->value.ToUint64(), 0x22u);
}

// §6.6.4: the strength of the value held in the capacitive state is small,
// medium, or large according to the size given in the trireg declaration.
TEST(TriregResolution, CapacitiveStrengthFollowsDeclaredSizeLarge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->InCapacitiveState());
  EXPECT_EQ(net->charge_strength, Strength::kLarge);
}

TEST(TriregResolution, CapacitiveStrengthFollowsDeclaredSizeSmall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (small) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->charge_strength, Strength::kSmall);
}

// The medium keyword is the third declared size; covering it exercises a parse
// path distinct from the implicit default below.
TEST(TriregResolution, CapacitiveStrengthFollowsDeclaredSizeMedium) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (medium) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->charge_strength, Strength::kMedium);
}

TEST(TriregResolution, CapacitiveStrengthDefaultsToMedium) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->charge_strength, Strength::kMedium);
}

// §6.6.4: in the driven state the strength on the net is that of the driver --
// supply, strong, pull, or weak -- not the capacitive (charge) strength.
TEST(TriregResolution, DrivenStrengthFollowsPullDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
}

TEST(TriregResolution, DrivenStrengthFollowsStrongDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
}

TEST(TriregResolution, DrivenStrengthFollowsWeakDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kWeak);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kWeak);
}

TEST(TriregResolution, DrivenStrengthFollowsSupplyDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kSupply);
}

}  // namespace
