#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static Logic4Word ResolveTwoBit(Arena& arena, NetType type, Logic4Word a,
                                Logic4Word b) {
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = type;
  net.resolved = var;
  auto da = MakeLogic4Vec(arena, 1);
  da.words[0] = a;
  auto db = MakeLogic4Vec(arena, 1);
  db.words[0] = b;
  net.drivers.push_back(da);
  net.drivers.push_back(db);
  net.Resolve(arena);
  return {var->value.words[0].aval & 1, var->value.words[0].bval & 1};
}

TEST(Tri0Tri1Resolution, Tri0_0_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_0_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_0_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_0_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_1_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_1_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_1_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_1_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_x_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_z_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_z_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_z_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_z_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_0_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_0_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_0_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_0_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_1_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_1_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_1_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_1_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_x_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_z_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_z_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_z_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_z_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0DrivenValuePassesThrough) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAB));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(Tri0Tri1Resolution, Tri1DrivenValuePassesThrough) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xCD));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(Tri0Tri1Resolution, Tri0UndrivenDefaultsToZeroWithPull) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
}

TEST(Tri0Tri1Resolution, Tri1UndrivenDefaultsToOneWithPull) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
}

TEST(Tri0Tri1Resolution, Tri0PullsOnlyResidualZBitsLowAcrossVector) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0] = {0x05, 0xF0};
  net.drivers.push_back(drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x05u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0x00u);
}

TEST(Tri0Tri1Resolution, Tri1PullsOnlyResidualZBitsHighAcrossVector) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0] = {0x05, 0xF0};
  net.drivers.push_back(drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xF5u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0x00u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0UndrivenIsKnownZeroNotHighZ) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 1'b0);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri1UndrivenReadsOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0HighZDriverPullsToZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(Tri0Tri1ResolutionE2e, Tri1HighZDriverPullsToOne) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'bz;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0StrongDriverOverridesPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri1StrongZeroDriverOverridesPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0WeakDriverLosesToPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign (weak1, weak0) w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(Tri0Tri1ResolutionE2e, Tri1WeakDriverLosesToPull) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign (weak1, weak0) w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = w;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0EqualPullDriverConflictsToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign (pull1, pull0) w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri1EqualPullDriverConflictsToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 w;\n"
                      "  logic result;\n"
                      "  assign (pull1, pull0) w = 1'b0;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0VectorResidualZPullsPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 [3:0] w;\n"
                      "  logic result;\n"
                      "  assign w = 4'bzz01;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 4'b0001);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri1VectorResidualZPullsPerBit) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri1 [3:0] w;\n"
                      "  logic result;\n"
                      "  assign w = 4'bzz01;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = (w === 4'b1101);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e, Tri0ConflictingStrongDriversResolveToX) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  tri0 w;\n"
                      "  logic result;\n"
                      "  assign w = 1'b0;\n"
                      "  assign w = 1'b1;\n"
                      "  initial begin\n"
                      "    #1;\n"
                      "    result = $isunknown(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(Tri0Tri1ResolutionE2e,
     StrongDriverGivesAStrongResultAndOnlyAllZGivesPull) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  tri0 n0;\n"
      "  tri1 n1;\n"
      "  reg v;\n"
      "  assign n0 = v;\n"
      "  assign n0 = 1'bz;\n"
      "  assign n1 = v;\n"
      "  assign n1 = 1'bz;\n"
      "  initial begin\n"
      "    v = 1'b1;\n"
      "    #1 $display(\"%v %v\", n0, n1);\n"
      "    v = 1'b0;\n"
      "    #1 $display(\"%v %v\", n0, n1);\n"
      "    v = 1'bz;\n"
      "    #1 $display(\"%v %v\", n0, n1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "St1 St1\nSt0 St0\nPu0 Pu1\n");
}

}  // namespace
