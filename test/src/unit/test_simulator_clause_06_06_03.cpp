#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- Table 6-3: wand/triand truth table ---

TEST(WiredNetResolution, Wand_0_0) {
  auto r = ResolveWandWord({0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_1) {
  auto r = ResolveWandWord({0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_x) {
  auto r = ResolveWandWord({0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_z) {
  auto r = ResolveWandWord({0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_1_0) {
  auto r = ResolveWandWord({1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_1_1) {
  auto r = ResolveWandWord({1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_1_x) {
  auto r = ResolveWandWord({1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_1_z) {
  auto r = ResolveWandWord({1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_x_0) {
  auto r = ResolveWandWord({0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_x_1) {
  auto r = ResolveWandWord({0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_x_x) {
  auto r = ResolveWandWord({0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_x_z) {
  auto r = ResolveWandWord({0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_z_0) {
  auto r = ResolveWandWord({1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_z_1) {
  auto r = ResolveWandWord({1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_z_x) {
  auto r = ResolveWandWord({1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_z_z) {
  auto r = ResolveWandWord({1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

// --- Table 6-4: wor/trior truth table ---

TEST(WiredNetResolution, Wor_0_0) {
  auto r = ResolveWorWord({0, 0}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_0_1) {
  auto r = ResolveWorWord({0, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_0_x) {
  auto r = ResolveWorWord({0, 0}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_0_z) {
  auto r = ResolveWorWord({0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_0) {
  auto r = ResolveWorWord({1, 0}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_1) {
  auto r = ResolveWorWord({1, 0}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_x) {
  auto r = ResolveWorWord({1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_z) {
  auto r = ResolveWorWord({1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_x_0) {
  auto r = ResolveWorWord({0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_x_1) {
  auto r = ResolveWorWord({0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_x_x) {
  auto r = ResolveWorWord({0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_x_z) {
  auto r = ResolveWorWord({0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_z_0) {
  auto r = ResolveWorWord({1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_z_1) {
  auto r = ResolveWorWord({1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_z_x) {
  auto r = ResolveWorWord({1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_z_z) {
  auto r = ResolveWorWord({1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

// --- Net::Resolve() integration tests ---

TEST(WiredNetResolution, ResolveWandNet) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(WiredNetResolution, ResolveWorNet) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(WiredNetResolution, TriandUsesWandResolution) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTriand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(WiredNetResolution, TriorUsesWorResolution) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrior;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

}  // namespace
