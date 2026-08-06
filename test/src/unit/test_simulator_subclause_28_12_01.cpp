#include <gtest/gtest.h>

#include "common/arena.h"
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

  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// --- Full-pipeline observation of the §28.12.1 rules ------------------------
// The three rules of §28.12.1 govern how the simulator resolves a wired net
// driven by two or more unambiguous drivers -- each carrying a known value and
// a single strength level. The drivers below are produced from real
// drive-strength continuous-assignment source (the machinery of §28.11),
// elaborated, lowered, and run, so the resolved value and strength are observed
// exactly as the production resolver computes them rather than from a
// hand-assembled Net.

// Elaborates, lowers, and runs `src`, then returns the settled net named "w".
static Net* RunAndFindNetW(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("w");
}

// Rule 1: drivers of unequal strength -> the stronger driver dominates the
// weaker ones and determines the result. Reproduces Figure 28-3: a pull1
// combined with a strong0 settles to strong0.
TEST(StrengthResolutionPipeline, UnequalStrengthStrongerDominates) {
  SimFixture f;
  Net* net = RunAndFindNetW(
      f,
      "module t;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"      // pull-strength 1 driver
      "  assign (strong0, strong1) w = 1'b0;\n"  // strong-strength 0 driver
      "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // strong0 dominates pull1
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

// Rule 2: drivers of like value -> the result carries that value with the
// greater of all the driving strengths.
TEST(StrengthResolutionPipeline, LikeValueTakesGreaterStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(
      f,
      "module t;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"      // pull-strength 1 driver
      "  assign (strong0, strong1) w = 1'b1;\n"  // strong-strength 1 driver
      "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);  // shared value preserved
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);  // greater wins
}

// Rule 3: drivers identical in strength and value -> the result is that same
// signal, at the same (unambiguous) strength.
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

// Rule 1, vector operand: resolution is applied independently per bit, so on a
// multi-bit net each bit is decided by its own stronger driver. Full-pipeline
// analog of the scalar case, exercising the vector operand type end to end.
TEST(StrengthResolutionPipeline, UnequalStrengthVectorResolvesPerBit) {
  SimFixture f;
  Net* net = RunAndFindNetW(
      f,
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign (weak0, weak1) w = 8'hFF;\n"      // weak drivers, all ones
      "  assign (strong0, strong1) w = 8'h0F;\n"  // strong drivers, low nibble
      "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);  // strong wins every bit
}

// Rule 1, drivers produced by gate primitives: §28.12.1 resolves the drivers of
// a wired net regardless of how they are produced. Here the two competing
// drivers originate from `and` gate outputs carrying drive strengths (§28.4
// gate syntax feeding the §28.11 strength machinery), built from real source.
TEST(StrengthResolutionPipeline, GateOutputDriversResolveByStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(
      f,
      "module t;\n"
      "  wire w;\n"
      "  wire a = 1'b1, b = 1'b1;\n"             // and -> 1
      "  wire c = 1'b0, d = 1'b1;\n"             // and -> 0
      "  and (weak0, weak1) g0(w, a, b);\n"      // weak-strength 1 driver
      "  and (strong0, strong1) g1(w, c, d);\n"  // strong-strength 0 driver
      "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // strong0 gate output dominates
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

// Rule 1, driver produced by a net-declaration assignment: a net declaration
// with a drive strength and an initializer is itself a continuous driver
// (§6.10), so it combines with a second driver under the same resolution rule.
TEST(StrengthResolutionPipeline, NetDeclInitializerDriverCombines) {
  SimFixture f;
  Net* net = RunAndFindNetW(
      f,
      "module t;\n"
      "  wire (pull0, pull1) w = 1'b1;\n"        // net-decl driver: pull 1
      "  assign (strong0, strong1) w = 1'b0;\n"  // cont-assign driver: strong 0
      "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // strong0 dominates the pull1 driver
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

}  // namespace
