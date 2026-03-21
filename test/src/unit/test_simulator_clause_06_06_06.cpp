#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SupplyNetResolution, Supply0AlwaysZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply0;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SupplyNetResolution, Supply1AlwaysOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply1;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFF, 0xFFu);
}

TEST(SupplyNetResolution, Supply0OverridesMultipleDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply0;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SupplyNetResolution, Supply1OverridesMultipleDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply1;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x55));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFF, 0xFFu);
}

TEST(SupplyNetResolution, Supply0IgnoresXDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply0;
  net.resolved = var;

  auto x_drv = MakeLogic4Vec(arena, 8);
  x_drv.words[0].aval = 0;
  x_drv.words[0].bval = 0xFF;
  net.drivers.push_back(x_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SupplyNetResolution, Supply1IgnoresZDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply1;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = ~uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFF, 0xFFu);
}

}  // namespace
