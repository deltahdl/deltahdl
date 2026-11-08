#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TriregResolution, TriregRetainsPrevValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();

  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TriregResolution, InCapacitiveStateWhenAllDriversZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 55);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  EXPECT_TRUE(net.InCapacitiveState());
}

TEST(TriregResolution, NotInCapacitiveStateWhenDriven) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, NotInCapacitiveStateForNonTrireg) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, MixedZAndDrivenResolvesToDriven) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TriregResolution, NotInCapacitiveStateWhenAnyDriverNonZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 55);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 1));
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, RetainsXStateWhenDriversTurnOff) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  var->value.words[0].aval = 0xFF;
  var->value.words[0].bval = 0xFF;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, RetainsPrevValueWhenAllOfMultipleDriversTurnOff) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 73);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv_a = MakeLogic4Vec(arena, 8);
  z_drv_a.words[0].aval = uint64_t{0};
  z_drv_a.words[0].bval = ~uint64_t{0};
  auto z_drv_b = MakeLogic4Vec(arena, 8);
  z_drv_b.words[0].aval = uint64_t{0};
  z_drv_b.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv_a);
  net.drivers.push_back(z_drv_b);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 73u);
  EXPECT_TRUE(net.InCapacitiveState());
}

TEST(TriregResolution, HoldsInitialZStateWhenUndriven) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  auto z_val = MakeLogic4Vec(arena, 8);
  z_val.words[0].aval = uint64_t{0};
  z_val.words[0].bval = ~uint64_t{0};
  var->value = z_val;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, XDriverResolvesLikeWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto x_drv = MakeLogic4Vec(arena, 8);
  x_drv.words[0].aval = 0xFF;
  x_drv.words[0].bval = 0xFF;
  net.drivers.push_back(x_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregChargeDecayRuntime, ForceHoldsZLogicState) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    force cap = 1'bz;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_TRUE(net->resolved->is_forced);
  EXPECT_EQ(net->resolved->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(net->resolved->value.words[0].bval & 1u, 1u);
}

TEST(TriregChargeDecayRuntime, ReleasingForceDropsHeldZAndFollowsDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    force cap = 1'bz;\n"
      "    #1;\n"
      "    release cap;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_FALSE(net->resolved->is_forced);
  EXPECT_FALSE(net->InCapacitiveState());
  EXPECT_EQ(net->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(net->resolved->value.words[0].bval & 1u, 0u);
}

TEST(TriregChargeDecayRuntime, ZeroDecayTimeDecaysWhenDriversTurnOff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg #(0, 0, 0) cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1 en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.words[0].bval & 1u, 1u);
}

TEST(TriregChargeDecayRuntime, AbsentThirdDelayHoldsTheChargeAfterTurnOff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  trireg #(0, 0) cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1 en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* net = f.ctx.FindNet("cap");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(net->resolved->value.words[0].bval & 1u, 0u);
}

TEST(TriregChargeStorage, SignalThroughASwitchDrivesTheTrireg) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  trireg t;\n"
      "  assign a = 1'b1;\n"
      "  tran (a, t);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* t = f.ctx.FindNet("t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->resolved->value.words[0].aval & 0x1, 1u);
  EXPECT_EQ(t->resolved->value.words[0].bval & 0x1, 0u);
  EXPECT_EQ(t->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(TriregChargeStorage, TriregNothingReachesThroughASwitchHoldsItsCharge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  trireg t;\n"
      "  tran (a, t);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* t = f.ctx.FindNet("t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->resolved->value.words[0].aval & 0x1, 1u);
  EXPECT_EQ(t->resolved->value.words[0].bval & 0x1, 1u);
  EXPECT_EQ(t->resolved_strength.s0_hi, Strength::kMedium);
  EXPECT_EQ(t->resolved_strength.s1_hi, Strength::kMedium);
}

TEST(TriregChargeStorage, ABitWhoseDriversTurnOffAloneKeepsItsCharge) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg e = 1;\n"
      "  trireg [1:0] t;\n"
      "  assign t[0] = e ? 1'b1 : 1'bz;\n"
      "  assign t[1] = 1'b1;\n"
      "  initial begin\n"
      "    #10 e = 0;\n"
      "    #1 $display(\"%b\", t);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "11\n");
}

TEST(TriregChargeStorage, ABitHoldingChargeAloneDecaysAlone) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg e = 1;\n"
      "  trireg [1:0] #(0, 0, 5) t;\n"
      "  assign t[0] = e ? 1'b1 : 1'bz;\n"
      "  assign t[1] = 1'b1;\n"
      "  initial begin\n"
      "    #10 e = 0;\n"
      "    #6 $display(\"%b\", t);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1x\n");
}

}  // namespace
