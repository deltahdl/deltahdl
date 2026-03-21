#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
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
  z_drv.words[0].aval = ~uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TriregResolution, TriregDrivenNormally) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TriregResolution, InCapacitiveStateWhenAllDriversZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 55);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = ~uint64_t{0};
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
  z_drv.words[0].aval = ~uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, MultipleZDriversRetainValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 77);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z1 = MakeLogic4Vec(arena, 8);
  z1.words[0].aval = ~uint64_t{0};
  z1.words[0].bval = ~uint64_t{0};
  auto z2 = MakeLogic4Vec(arena, 8);
  z2.words[0].aval = ~uint64_t{0};
  z2.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z1);
  net.drivers.push_back(z2);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TriregResolution, MultipleDrivenDriversResolve) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(TriregResolution, XDriverResolvesLikeWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  // Single x driver: all bits x (aval=0, bval=all-ones).
  auto x_drv = MakeLogic4Vec(arena, 8);
  x_drv.words[0].aval = 0;
  x_drv.words[0].bval = 0xFF;
  net.drivers.push_back(x_drv);
  net.Resolve(arena);
  // x driver is not z, so net is driven — should resolve to x.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

}  // namespace
