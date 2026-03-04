#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NetResolution, WandZeroDominates) {

  Logic4Word a{0, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWandWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WandBothOne) {

  Logic4Word a{1, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWandWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WandXWithOne) {

  Logic4Word x{0, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWandWord(x, one);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(NetResolution, WandXWithZero) {

  Logic4Word x{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWandWord(x, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WorOneDominates) {

  Logic4Word a{1, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWorWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WorBothZero) {

  Logic4Word a{0, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWorWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WorXWithZero) {

  Logic4Word x{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWorWord(x, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(NetResolution, WorXWithOne) {

  Logic4Word x{0, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWorWord(x, one);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, ResolveWandNet) {
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

TEST(NetResolution, ResolveWorNet) {
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

}
