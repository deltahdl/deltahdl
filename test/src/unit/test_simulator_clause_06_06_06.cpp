// §6.6.6: Supply nets

#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

// --- §6.6.6: Supply net resolution ---
TEST(NetResolution, Supply0AlwaysZero) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply0;
  net.resolved = var;
  // Driver tries to drive 0xFF — supply0 should override to 0.
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(NetResolution, Supply1AlwaysOne) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply1;
  net.resolved = var;
  // Driver tries to drive 0x00 — supply1 should override to all-1.
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFF, 0xFFu);
}

TEST(NetResolution, Supply0OverridesMultipleDrivers) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kSupply0;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
