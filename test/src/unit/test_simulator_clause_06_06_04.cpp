#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_logic4vec_z.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static Logic4Vec MakeXVec(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval = ~uint64_t{0};  // canonical Convention A: x = (1, 1)
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
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0xFFu);  // x = (aval=1, bval=1)
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
// medium, or large according to the size given in the trireg declaration. The
// large size is exercised by CapacitiveStateStrengthComesFromDeclaredSize
// below, which additionally observes the declared size surfacing as the
// resolved strength; only the small/medium/default forms are checked here.
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

// §6.6.4: the size named in the trireg declaration is not merely recorded -- it
// is the strength that the held value carries once the net enters the
// capacitive state. Build the declared size and its driver entirely from real
// source: a large-size trireg driven through a §28 continuous assignment that
// is switched to the high-impedance value. After the driver is released the
// whole design is run, and the resolution is observed surfacing that declared
// size (large) as the strength of the retained value.
TEST(TriregResolution, CapacitiveStateStrengthComesFromDeclaredSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg (large) cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // drive cap to 1
      "    #1;\n"
      "    en = 1'b0;\n"  // release the driver to z -> capacitive state
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_EQ(net->charge_strength, Strength::kLarge);
  EXPECT_TRUE(net->InCapacitiveState());
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.ToUint64() & 1u, 1u);  // held 1
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kLarge);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kLarge);
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

// ---------------------------------------------------------------------------
// End-to-end observations of §6.6.4's driven/capacitive rules, with the drivers
// built from the §28 dependency's real source: a bare continuous assignment, a
// conditional assignment that can go high-impedance, and a drive-strength
// specification. Each design is elaborated, lowered, and simulated, and the
// resolved trireg value/strength is read back from the SimContext -- the rule
// is observed exactly as production resolves the net during a run, not through
// a hand-built Net.
// ---------------------------------------------------------------------------

// §6.6.4 driven state, driver value 1: a continuous assignment carrying 1
// places the trireg in the driven state and that value propagates onto the net.
TEST(TriregResolution, DrivenStateTakesContinuousAssignOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "  assign cap = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindVariable("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.words[0].aval & 1u, 1u);  // 1 = (aval=1, bval=0)
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

// §6.6.4 driven state, driver value 0: because an undriven trireg defaults to
// x, observing 0 confirms the driven value took over rather than the default.
TEST(TriregResolution, DrivenStateTakesContinuousAssignZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "  assign cap = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindVariable("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.words[0].aval & 1u, 0u);  // 0 = (aval=0, bval=0)
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

// §6.6.4 driven state, driver value x: x is a driving value, so driving x over
// a net that was previously holding 1 replaces the value -- x propagates into
// the driven net rather than being blocked the way the high-impedance value is.
TEST(TriregResolution, DrivenStateTakesContinuousAssignUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  trireg cap;\n"
      "  assign cap = sel ? 1'bx : 1'b1;\n"
      "  initial begin\n"
      "    sel = 1'b0;\n"  // drive cap to 1
      "    #1;\n"
      "    sel = 1'b1;\n"  // drive x over the held 1
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindVariable("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(cap->value.words[0].bval & 1u, 1u);
}

// §6.6.4 capacitive state, retained 1: drive the net to 1 through a conditional
// assignment, then let the driver go to z. The trireg must hold the last driven
// 1 -- the high-impedance value does not propagate into it.
TEST(TriregResolution, CapacitiveStateHoldsOneAfterDriverGoesHighZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->InCapacitiveState());
  auto* cap = f.ctx.FindVariable("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.words[0].aval & 1u, 1u);  // held 1, not z
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

// §6.6.4 capacitive state, retained 0: the stored value can be 0 as well. Since
// an undriven trireg defaults to x, holding 0 after the driver is released
// shows the net stored its last driven value rather than reverting to the
// default.
TEST(TriregResolution, CapacitiveStateHoldsZeroAfterDriverGoesHighZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg cap;\n"
      "  assign cap = en ? 1'b0 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->InCapacitiveState());
  auto* cap = f.ctx.FindVariable("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.words[0].aval & 1u, 0u);  // held 0, not x/z
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

// §6.6.4 driven strength (weak): in the driven state the strength on the net is
// the driver's strength. A weak-strength continuous assignment drives the net
// weakly -- the resolved drive strength is weak, not the capacitive size.
TEST(TriregResolution, DrivenStrengthTracksWeakContinuousAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "  assign (weak1, weak0) cap = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_FALSE(net->InCapacitiveState());
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kWeak);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kWeak);
}

// §6.6.4 driven strength (supply): the strongest driver strength likewise
// carries onto the net while it is driven.
TEST(TriregResolution, DrivenStrengthTracksSupplyContinuousAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "  assign (supply1, supply0) cap = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  EXPECT_FALSE(net->InCapacitiveState());
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kSupply);
}

}  // namespace
