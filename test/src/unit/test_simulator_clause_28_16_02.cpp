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

TEST(TriregResolution, MixedZAndDrivenResolvesToDriven) {
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
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TriregResolution, NotInCapacitiveStateWhenAnyDriverNonZ) {
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
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 1));
  EXPECT_FALSE(net.InCapacitiveState());
}

TEST(TriregResolution, RetainsXStateWhenDriversTurnOff) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  var->value.words[0].aval = 0;
  var->value.words[0].bval = 0xFF;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = ~uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, RetainsPrevValueWhenAllOfMultipleDriversTurnOff) {
  // §28.16.2: when the drivers of a trireg transition to off (z), the net keeps
  // the last 1/0/x value it held and z never propagates onto it. Exercise the
  // multi-driver case where every driver has turned off simultaneously.
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 73);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto z_drv_a = MakeLogic4Vec(arena, 8);
  z_drv_a.words[0].aval = ~uint64_t{0};
  z_drv_a.words[0].bval = ~uint64_t{0};
  auto z_drv_b = MakeLogic4Vec(arena, 8);
  z_drv_b.words[0].aval = ~uint64_t{0};
  z_drv_b.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv_a);
  net.drivers.push_back(z_drv_b);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 73u);
  EXPECT_TRUE(net.InCapacitiveState());
}

TEST(TriregResolution, HoldsZWhenForcedEvenWithActiveDriver) {
  // §28.16.2: a trireg can hold a z logic state when the net is forced to z
  // (see §10.6.2). A forced net keeps its z value even though a driver is
  // actively driving a non-z value into the net.
  Arena arena;
  auto* var = arena.Create<Variable>();
  auto z_val = MakeLogic4Vec(arena, 8);
  z_val.words[0].aval = ~uint64_t{0};
  z_val.words[0].bval = ~uint64_t{0};
  var->value = z_val;
  var->is_forced = true;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 1));
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, HoldsInitialZStateWhenUndriven) {
  // §28.16.2: a trireg can hold a z logic state when z is the initial logic
  // state of the net. With no drivers present nothing charges the storage
  // node, so the initial z persists.
  Arena arena;
  auto* var = arena.Create<Variable>();
  auto z_val = MakeLogic4Vec(arena, 8);
  z_val.words[0].aval = ~uint64_t{0};
  z_val.words[0].bval = ~uint64_t{0};
  var->value = z_val;
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  // No drivers added: the trireg is undriven from elaboration onward.
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(TriregResolution, XDriverResolvesLikeWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  auto x_drv = MakeLogic4Vec(arena, 8);
  x_drv.words[0].aval = 0;
  x_drv.words[0].bval = 0xFF;
  net.drivers.push_back(x_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

}  // namespace
