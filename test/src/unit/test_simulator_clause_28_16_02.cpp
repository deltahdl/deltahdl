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

// §28.16.2 R8: a z value on one driver must not propagate to the trireg
// — when another driver is non-z, the non-z driver wins and the trireg
// takes that value rather than going into capacitive retention.
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

// §28.16.2 R8: the capacitive predicate must require every driver to be
// z — a single non-z driver pulls the trireg out of capacitive state
// because the z drivers never contribute, leaving only the non-z one.
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
