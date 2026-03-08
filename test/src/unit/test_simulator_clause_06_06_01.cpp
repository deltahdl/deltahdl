#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(WireTriResolution, Wire_0_0) {
  Logic4Word a{0, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_0_1) {
  Logic4Word a{0, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_0_x) {
  Logic4Word zero{0, 0};
  Logic4Word x{0, 1};
  auto r = ResolveWireWord(zero, x);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_0_z) {
  Logic4Word zero{0, 0};
  Logic4Word z{1, 1};
  auto r = ResolveWireWord(zero, z);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_1_0) {
  Logic4Word one{1, 0};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(one, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_1_1) {
  Logic4Word a{1, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_1_x) {
  Logic4Word one{1, 0};
  Logic4Word x{0, 1};
  auto r = ResolveWireWord(one, x);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_1_z) {
  Logic4Word one{1, 0};
  Logic4Word z{1, 1};
  auto r = ResolveWireWord(one, z);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_x_0) {
  Logic4Word x{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(x, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_x_1) {
  Logic4Word x{0, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWireWord(x, one);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_x_x) {
  Logic4Word x{0, 1};
  auto r = ResolveWireWord(x, x);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_x_z) {
  Logic4Word x{0, 1};
  Logic4Word z{1, 1};
  auto r = ResolveWireWord(x, z);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_z_0) {
  Logic4Word z{1, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(z, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_z_1) {
  Logic4Word z{1, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWireWord(z, one);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(WireTriResolution, Wire_z_x) {
  Logic4Word z{1, 1};
  Logic4Word x{0, 1};
  auto r = ResolveWireWord(z, x);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, Wire_z_z) {
  Logic4Word z{1, 1};
  auto r = ResolveWireWord(z, z);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(WireTriResolution, ResolveSingleDriverWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 42));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(WireTriResolution, ResolveMultipleDriversAgreeWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(WireTriResolution, ResolveMultipleDriversConflictWire) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(WireTriResolution, ResolveEmptyDriversNoChange) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 99);
  Net net;
  net.resolved = var;

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(WireTriResolution, TriUsesWireResolution) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(WireTriResolution, TriConflictProducesX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(WireTriResolution, TriSingleDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAB));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(WireTriResolution, ThreeDriverWireResolution) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0011));
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0101));
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0001));

  net.Resolve(arena);

  auto w = var->value.words[0];

  EXPECT_TRUE((w.aval & 1u) != 0);
  EXPECT_TRUE((w.bval & 1u) == 0);

  EXPECT_TRUE((w.aval & 2u) == 0);
  EXPECT_TRUE((w.bval & 2u) != 0);

  EXPECT_TRUE((w.aval & 4u) == 0);
  EXPECT_TRUE((w.bval & 4u) != 0);

  EXPECT_TRUE((w.aval & 8u) == 0);
  EXPECT_TRUE((w.bval & 8u) == 0);
}

}
