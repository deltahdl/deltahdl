#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Helper: resolve two 1-bit drivers on a net of the given type.
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

// --- Table 6-5: tri0 truth table (16 entries) ---

TEST(Tri0Tri1Resolution, Tri0_0_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_0_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_0_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_0_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_1_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
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
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_1_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_x_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_x_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_z_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_z_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri0_z_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri0_z_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri0, {1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

// --- Table 6-6: tri1 truth table (16 entries) ---

TEST(Tri0Tri1Resolution, Tri1_0_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_0_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_0_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_0_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_1_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
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
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_1_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_x_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_x_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_z_0) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_z_1) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(Tri0Tri1Resolution, Tri1_z_x) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(Tri0Tri1Resolution, Tri1_z_z) {
  Arena arena;
  auto r = ResolveTwoBit(arena, NetType::kTri1, {1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

// Driven value passes through unchanged.
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

}  // namespace
