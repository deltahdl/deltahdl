#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  auto r = ResolveWandWord({0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_0_z) {
  auto r = ResolveWandWord({0, 0}, {0, 1});
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
  auto r = ResolveWandWord({1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_1_z) {
  auto r = ResolveWandWord({1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_x_0) {
  auto r = ResolveWandWord({1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_x_1) {
  auto r = ResolveWandWord({1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_x_x) {
  auto r = ResolveWandWord({1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_x_z) {
  auto r = ResolveWandWord({1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_z_0) {
  auto r = ResolveWandWord({0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_z_1) {
  auto r = ResolveWandWord({0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wand_z_x) {
  auto r = ResolveWandWord({0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wand_z_z) {
  auto r = ResolveWandWord({0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

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
  auto r = ResolveWorWord({0, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_0_z) {
  auto r = ResolveWorWord({0, 0}, {0, 1});
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
  auto r = ResolveWorWord({1, 0}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_1_z) {
  auto r = ResolveWorWord({1, 0}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_x_0) {
  auto r = ResolveWorWord({1, 1}, {0, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_x_1) {
  auto r = ResolveWorWord({1, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_x_x) {
  auto r = ResolveWorWord({1, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_x_z) {
  auto r = ResolveWorWord({1, 1}, {0, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_z_0) {
  auto r = ResolveWorWord({0, 1}, {0, 0});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_z_1) {
  auto r = ResolveWorWord({0, 1}, {1, 0});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WiredNetResolution, Wor_z_x) {
  auto r = ResolveWorWord({0, 1}, {1, 1});
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WiredNetResolution, Wor_z_z) {
  auto r = ResolveWorWord({0, 1}, {0, 1});
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

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

// Builds an all-z value of the given width. Canonical Convention A encodes z as
// (aval=0, bval=1) per bit.
Logic4Vec MakeZVec(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1);
  v.words[0].aval = 0;
  v.words[0].bval = mask;
  return v;
}

// §6.6.3 wired-AND, edge case: a high-impedance driver does not dominate; the
// resolved net through Net::Resolve takes the value of the defined driver.
TEST(WiredNetResolution, WandHighZDriverYieldsToDefined) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeZVec(arena, 8));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

// §6.6.3 wired-OR, edge case: a high-impedance driver does not dominate; the
// resolved net through Net::Resolve takes the value of the defined driver.
TEST(WiredNetResolution, WorHighZDriverYieldsToDefined) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeZVec(arena, 8));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

// §6.6.3: "if any driver is 0, the value of the net is 0." Exercises the
// multi-driver fold in Net::Resolve with more than two drivers; the lone 0 bit
// in the third driver pulls that bit of the wired-AND net to 0.
TEST(WiredNetResolution, WandThreeDriversAnyZeroIsZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

// §6.6.3: "when any of the drivers is 1, the resulting value of the net is 1."
// Exercises the multi-driver fold in Net::Resolve with more than two drivers;
// the lone 1 bits in the third driver pull those bits of the wired-OR net to 1.
TEST(WiredNetResolution, WorThreeDriversAnyOneIsOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x00));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x00));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

}  // namespace
