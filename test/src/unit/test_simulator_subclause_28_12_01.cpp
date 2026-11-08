#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthResolution, StrongerDriverWinsPerBit) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(StrengthResolution, ThreeDriversStrongestWins) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, HighzDriverIgnored) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, AllHighzProducesZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToString(), "z");
}

static Net* RunAndFindNetW(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("w");
}

TEST(StrengthResolutionPipeline, UnequalStrengthStrongerDominates) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  assign (pull0, pull1) w = 1'b1;\n"
                            "  assign (strong0, strong1) w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

TEST(StrengthResolutionPipeline, LikeValueTakesGreaterStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  assign (pull0, pull1) w = 1'b1;\n"
                            "  assign (strong0, strong1) w = 1'b1;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthResolutionPipeline, IdenticalDriversYieldSameSignal) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  assign (pull0, pull1) w = 1'b0;\n"
                            "  assign (pull0, pull1) w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kPull);
  EXPECT_FALSE(net->resolved_strength.IsAmbiguous());
}

TEST(StrengthResolutionPipeline, UnequalStrengthVectorResolvesPerBit) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire [7:0] w;\n"
                            "  wire [7:0] ones = 8'hFF, low = 8'h0F;\n"
                            "  buf (weak0, weak1) gw[7:0] (w, ones);\n"
                            "  buf (strong0, strong1) gs[7:0] (w, low);\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(StrengthResolutionPipeline, GateOutputDriversResolveByStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  wire a = 1'b1, b = 1'b1;\n"
                            "  wire c = 1'b0, d = 1'b1;\n"
                            "  and (weak0, weak1) g0(w, a, b);\n"
                            "  and (strong0, strong1) g1(w, c, d);\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

TEST(StrengthResolutionPipeline, NetDeclInitializerDriverCombines) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire (pull0, pull1) w = 1'b1;\n"
                            "  assign (strong0, strong1) w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

TEST(StrengthResolutionPipeline, InterfaceNetDriversCombineByStrength) {
  SimFixture f;
  auto out = RunCapture(
      "interface bus;\n"
      "  wire y;\n"
      "endinterface\n"
      "module drv (bus b, input a);\n"
      "  buf (weak1, weak0) g1 (b.y, a);\n"
      "endmodule\n"
      "module top;\n"
      "  bus b();\n"
      "  logic a = 1;\n"
      "  drv d (b, a);\n"
      "  assign (pull1, pull0) b.y = 0;\n"
      "  initial #1 $display(\"y=%b %v\", b.y, b.y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=0 Pu0\n");
}

}  // namespace
