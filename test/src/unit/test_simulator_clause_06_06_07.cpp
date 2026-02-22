// §6.6.7: User-defined nettypes

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

using namespace delta;

enum class NettypeDataKind : uint8_t {
  k4StateIntegral,
  k2StateIntegral,
  kReal,
  kShortreal,
  kFixedUnpackedArray,
  kDynamicArray,
  kString,
  kClass,
};

using ResolutionFn =
    std::function<Logic4Vec(Arena &, const std::vector<Logic4Vec> &)>;

struct UserNettype {
  NettypeDataKind data_kind = NettypeDataKind::k4StateIntegral;
  uint32_t bit_width = 1;
  ResolutionFn resolution;
};

bool ValidateNettypeDataKind(NettypeDataKind kind);
bool ResolveUserDefinedNet(Net &net, const UserNettype &nettype, Arena &arena);
bool CheckUnresolvedMultipleDrivers(const Net &net, const UserNettype &nt);

bool ValidateNettypeDataKind(NettypeDataKind kind) {
  switch (kind) {
  case NettypeDataKind::k4StateIntegral:
  case NettypeDataKind::k2StateIntegral:
  case NettypeDataKind::kReal:
  case NettypeDataKind::kShortreal:
  case NettypeDataKind::kFixedUnpackedArray:
    return true;
  case NettypeDataKind::kDynamicArray:
  case NettypeDataKind::kString:
  case NettypeDataKind::kClass:
    return false;
  }
  return false;
}

bool ResolveUserDefinedNet(Net &net, const UserNettype &nettype, Arena &arena) {
  if (nettype.resolution) {
    Logic4Vec result = nettype.resolution(arena, net.drivers);
    net.resolved->value = result;
  }
  return true;
}

bool CheckUnresolvedMultipleDrivers(const Net &net, const UserNettype &nt) {
  return !nt.resolution && net.drivers.size() > 1;
}

static Variable *MakeVar(Arena &arena, uint32_t width) {
  auto *v = arena.Create<Variable>();
  v->value = MakeLogic4Vec(arena, width);
  return v;
}

static Net MakeDrivenNet(Arena &arena, Variable *var, uint64_t val) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, val));
  return net;
}

static Net MakeMultiDriverNet(Arena &arena, Variable *var,
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
  auto *var = MakeVar(arena, 1);
  Net net = MakeMultiDriverNet(arena, var, {1, 0});

  bool called = false;
  UserNettype nt;
  nt.resolution = [&](Arena &a,
                      const std::vector<Logic4Vec> &drivers) -> Logic4Vec {
    called = true;
    EXPECT_EQ(drivers.size(), 2u);
    return MakeLogic4VecVal(a, 1, 1);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(called);
}

TEST(UserDefinedNettype, DriverChangeTriggerResolution) {
  Arena arena;
  auto *var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 0);

  int call_count = 0;
  UserNettype nt;
  nt.resolution = [&](Arena &a,
                      const std::vector<Logic4Vec> &drivers) -> Logic4Vec {
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
  auto *var = MakeVar(arena, 1);
  Net net = MakeMultiDriverNet(arena, var, {1, 0});

  UserNettype nt;
  nt.resolution = nullptr;
  EXPECT_TRUE(CheckUnresolvedMultipleDrivers(net, nt));
}

TEST(UserDefinedNettype, UnresolvedNettypeSingleDriverOk) {
  Arena arena;
  auto *var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 1);

  UserNettype nt;
  nt.resolution = nullptr;
  EXPECT_FALSE(CheckUnresolvedMultipleDrivers(net, nt));
}

TEST(UserDefinedNettype, SameDataTypeDifferentResolution) {
  Arena arena;
  auto *var_a = MakeVar(arena, 1);
  auto *var_b = MakeVar(arena, 1);

  UserNettype nt_or;
  nt_or.resolution = [](Arena &a,
                        const std::vector<Logic4Vec> &drivers) -> Logic4Vec {
    uint64_t r = 0;
    for (const auto &d : drivers)
      r |= (d.words[0].aval & 1);
    return MakeLogic4VecVal(a, 1, r);
  };

  UserNettype nt_and;
  nt_and.resolution = [](Arena &a,
                         const std::vector<Logic4Vec> &drivers) -> Logic4Vec {
    uint64_t r = 1;
    for (const auto &d : drivers)
      r &= (d.words[0].aval & 1);
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
  auto *var = MakeVar(arena, 8);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x55));

  bool received_both = false;
  UserNettype nt;
  nt.bit_width = 8;
  nt.resolution = [&](Arena &a,
                      const std::vector<Logic4Vec> &drivers) -> Logic4Vec {
    received_both = (drivers.size() == 2);
    return MakeLogic4VecVal(a, 8, 0xFF);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_TRUE(received_both);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
}

TEST(UserDefinedNettype, ForceOverridesResolvedValue) {
  Arena arena;
  auto *var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 1);

  UserNettype nt;
  nt.resolution = [](Arena &a, const std::vector<Logic4Vec> &d) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, d[0].words[0].aval & 1);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);

  var->value = MakeLogic4VecVal(arena, 1, 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

TEST(UserDefinedNettype, ReleaseRestoresResolvedValue) {
  Arena arena;
  auto *var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 1);

  UserNettype nt;
  nt.resolution = [](Arena &a, const std::vector<Logic4Vec> &d) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, d[0].words[0].aval & 1);
  };

  var->value = MakeLogic4VecVal(arena, 1, 0);
  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}
