#include <gtest/gtest.h>

#include "common/arena.h"
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

// §6.6.5: with no driver connected, a tri0 net settles to 0 carrying pull
// strength (the implicit resistive pulldown), not the default high-impedance.
TEST(Tri0Tri1Resolution, Tri0UndrivenDefaultsToZeroWithPull) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  // No drivers connected to the net.
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
}

// §6.6.5: with no driver connected, a tri1 net settles to 1 carrying pull
// strength (the implicit resistive pullup).
TEST(Tri0Tri1Resolution, Tri1UndrivenDefaultsToOneWithPull) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  // No drivers connected to the net.
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
}

// §6.6.5: a tri0 net is equivalent to a wire driven by a continuous 0 of pull
// strength. Within one vector, an actual driver wins on the bits it drives,
// while every bit it leaves at z falls to the pulldown value 0. Exercises the
// per-bit residual-z fixup across a multi-bit net (low nibble driven, high
// nibble left floating).
TEST(Tri0Tri1Resolution, Tri0PullsOnlyResidualZBitsLowAcrossVector) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  // Bits 0-3 drive 1,0,1,0; bits 4-7 are z (aval&bval both set).
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0] = {0x05,
                  0xF0};  // low nibble driven; high nibble z=(aval0,bval1)
  net.drivers.push_back(drv);
  net.Resolve(arena);
  // Driven bits pass through unchanged; floating bits pull down to 0.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x05u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0x00u);
}

// §6.6.5: a tri1 net is equivalent to a wire driven by a continuous 1 of pull
// strength. The driven bits pass through; the floating bits pull up to 1.
TEST(Tri0Tri1Resolution, Tri1PullsOnlyResidualZBitsHighAcrossVector) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  // Bits 0-3 drive 1,0,1,0; bits 4-7 are z.
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0] = {0x05,
                  0xF0};  // low nibble driven; high nibble z=(aval0,bval1)
  net.drivers.push_back(drv);
  net.Resolve(arena);
  // Driven bits pass through unchanged; floating bits pull up to 1.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xF5u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0x00u);
}

}  // namespace
