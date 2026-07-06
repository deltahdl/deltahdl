#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "helpers_switch_network.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

// NettypeDataKind, UserNettype, and the resolution helpers exercised below
// are production declarations from simulator/net.h (§6.6.7).

static Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4Vec(arena, width);
  return v;
}

static Net MakeDrivenNet(Arena& arena, Variable* var, uint64_t val) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, val));
  return net;
}

static Net MakeMultiDriverNet(Arena& arena, Variable* var,
                              std::initializer_list<uint64_t> vals) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  for (uint64_t v : vals) {
    net.drivers.push_back(MakeLogic4VecVal(arena, 1, v));
  }
  return net;
}

TEST(UserDefinedNettype, ValidDataType4StateIntegral) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::k4StateIntegral));
}

TEST(UserDefinedNettype, ValidDataType2StateIntegral) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::k2StateIntegral));
}

TEST(UserDefinedNettype, ValidDataTypeReal) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::kReal));
}

TEST(UserDefinedNettype, ValidDataTypeShortreal) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::kShortreal));
}

TEST(UserDefinedNettype, ValidDataTypeFixedUnpackedArray) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::kFixedUnpackedArray));
}

TEST(UserDefinedNettype, InvalidDataTypeDynamicArray) {
  EXPECT_FALSE(ValidateNettypeDataKind(NettypeDataKind::kDynamicArray));
}

TEST(UserDefinedNettype, InvalidDataTypeString) {
  EXPECT_FALSE(ValidateNettypeDataKind(NettypeDataKind::kString));
}

TEST(UserDefinedNettype, InvalidDataTypeClass) {
  EXPECT_FALSE(ValidateNettypeDataKind(NettypeDataKind::kClass));
}

TEST(UserDefinedNettype, ResolutionFunctionCalledWithDriverValues) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeMultiDriverNet(arena, var, {1, 0});

  bool called = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    called = true;
    EXPECT_EQ(drivers.size(), 2u);
    return MakeLogic4VecVal(a, 1, 1);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(called);
}

TEST(UserDefinedNettype, DriverChangeTriggerResolution) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 0);

  int call_count = 0;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    ++call_count;
    return MakeLogic4VecVal(a, 1, drivers[0].words[0].aval & 1);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(call_count, 1);

  net.drivers[0] = MakeLogic4VecVal(arena, 1, 1);
  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(call_count, 2);
}

TEST(UserDefinedNettype, UnresolvedNettypeMultipleDriversIsError) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeMultiDriverNet(arena, var, {1, 0});

  UserNettype nt;
  nt.resolution = nullptr;
  EXPECT_TRUE(CheckUnresolvedMultipleDrivers(net, nt));
}

TEST(UserDefinedNettype, UnresolvedNettypeSingleDriverOk) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 1);

  UserNettype nt;
  nt.resolution = nullptr;
  EXPECT_FALSE(CheckUnresolvedMultipleDrivers(net, nt));
}

TEST(UserDefinedNettype, SameDataTypeDifferentResolution) {
  Arena arena;
  auto* var_a = MakeVar(arena, 1);
  auto* var_b = MakeVar(arena, 1);

  UserNettype nt_or;
  nt_or.resolution = [](Arena& a,
                        const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    uint64_t r = 0;
    for (const auto& d : drivers) r |= (d.words[0].aval & 1);
    return MakeLogic4VecVal(a, 1, r);
  };

  UserNettype nt_and;
  nt_and.resolution = [](Arena& a,
                         const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    uint64_t r = 1;
    for (const auto& d : drivers) r &= (d.words[0].aval & 1);
    return MakeLogic4VecVal(a, 1, r);
  };

  Net net_a = MakeMultiDriverNet(arena, var_a, {1, 0});
  Net net_b = MakeMultiDriverNet(arena, var_b, {1, 0});

  ResolveUserDefinedNet(net_a, nt_or, arena);
  ResolveUserDefinedNet(net_b, nt_and, arena);

  EXPECT_EQ(var_a->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var_b->value.words[0].aval & 1, 0u);
}

TEST(UserDefinedNettype, AtomicNetResolvedAsWhole) {
  Arena arena;
  auto* var = MakeVar(arena, 8);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x55));

  bool received_both = false;
  UserNettype nt;
  nt.bit_width = 8;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    received_both = (drivers.size() == 2);
    return MakeLogic4VecVal(a, 8, 0xFF);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(received_both);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
}

TEST(UserDefinedNettype, ForceOverridesResolvedValue) {
  // §6.6.7: a force overrides the value of a user-defined nettype net. Net
  // resolution leaves a forced net untouched -- observed through Net::Resolve.
  Arena arena;
  auto* var = MakeVar(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.is_user_nettype = true;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAB));

  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xABu);

  var->is_forced = true;
  var->value = MakeLogic4VecVal(arena, 8, 0x55);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x55u);
}

TEST(UserDefinedNettype, ReleaseRestoresResolvedValue) {
  // §6.6.7: once a forced nettype net is released, resolution again drives it,
  // returning the net to its resolved value -- observed through Net::Resolve.
  Arena arena;
  auto* var = MakeVar(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.is_user_nettype = true;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAB));

  var->is_forced = true;
  var->value = MakeLogic4VecVal(arena, 8, 0x55);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x55u);

  var->is_forced = false;
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xABu);
}

TEST(UserDefinedNettype, UnresolvedNettypeNoResolutionFunction) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  UserNettype nt;

  ResolveUserDefinedNet(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(UserDefinedNettype, ResolutionWithThreeDrivers) {
  Arena arena;
  auto* var = MakeVar(arena, 1);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));

  size_t driver_count = 0;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    driver_count = drivers.size();
    uint64_t result = 0;
    for (const auto& d : drivers) result |= (d.words[0].aval & 1);
    return MakeLogic4VecVal(a, 1, result);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(driver_count, 3u);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}
