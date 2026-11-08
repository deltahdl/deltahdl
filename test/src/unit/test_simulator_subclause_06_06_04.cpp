#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
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
    v.words[w].aval = ~uint64_t{0};
    v.words[w].bval = ~uint64_t{0};
  }
  return v;
}

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
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFFu, 0xFFu);
}

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

  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_TRUE(net.InCapacitiveState());
  EXPECT_EQ(var->value.ToUint64(), 0x7Eu);
  EXPECT_FALSE(IsAllZ(var->value));
}

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

TEST(TriregResolution, CapacitiveStateStrengthComesFromDeclaredSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg (large) cap;\n"
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
  ASSERT_EQ(net->charge_strength, Strength::kLarge);
  EXPECT_TRUE(net->InCapacitiveState());
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kLarge);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kLarge);
}

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
  EXPECT_EQ(cap->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

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
  EXPECT_EQ(cap->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

TEST(TriregResolution, DrivenStateTakesContinuousAssignUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  trireg cap;\n"
      "  assign cap = sel ? 1'bx : 1'b1;\n"
      "  initial begin\n"
      "    sel = 1'b0;\n"
      "    #1;\n"
      "    sel = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindVariable("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->value.words[0].bval & 1u, 1u);
}

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
  EXPECT_EQ(cap->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

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
  EXPECT_EQ(cap->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(cap->value.words[0].bval & 1u, 0u);
}

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

TEST(TriregResolution, VectoredTriregEntersCapacitiveStateAndHoldsItsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg (large) [7:0] cap;\n"
      "  assign cap = en ? 8'hA5 : 8'bz;\n"
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
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.ToUint64() & 0xFFu, 0xA5u);
}

}  // namespace
