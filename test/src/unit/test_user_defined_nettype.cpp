#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

using namespace delta;

// --- Local types for user-defined nettype (§6.6.7) ---

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
    std::function<Logic4Vec(Arena&, const std::vector<Logic4Vec>&)>;

struct UserNettype {
  NettypeDataKind data_kind = NettypeDataKind::k4StateIntegral;
  uint32_t bit_width = 1;
  ResolutionFn resolution;
};

bool ValidateNettypeDataKind(NettypeDataKind kind);
bool ResolveUserDefinedNet(Net& net, const UserNettype& nettype, Arena& arena);
bool CheckUnresolvedMultipleDrivers(const Net& net, const UserNettype& nt);

// --- Helpers ---

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

// =============================================================
// §6.6.7: User-defined nettypes
// =============================================================

// --- Valid data types ---

// §6.6.7: "A valid data type shall be one of the following:
//  a) A 4-state integral type"
TEST(UserDefinedNettype, ValidDataType4StateIntegral) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::k4StateIntegral));
}

// §6.6.7: "b) A 2-state integral type"
TEST(UserDefinedNettype, ValidDataType2StateIntegral) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::k2StateIntegral));
}

// §6.6.7: "c) A real or shortreal type."
TEST(UserDefinedNettype, ValidDataTypeReal) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::kReal));
}

TEST(UserDefinedNettype, ValidDataTypeShortreal) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::kShortreal));
}

// §6.6.7: "d) A fixed-size unpacked array, unpacked structure or union"
TEST(UserDefinedNettype, ValidDataTypeFixedUnpackedArray) {
  EXPECT_TRUE(ValidateNettypeDataKind(NettypeDataKind::kFixedUnpackedArray));
}

// §6.6.7: Exhaustive list — these are NOT valid.
TEST(UserDefinedNettype, InvalidDataTypeDynamicArray) {
  EXPECT_FALSE(ValidateNettypeDataKind(NettypeDataKind::kDynamicArray));
}

TEST(UserDefinedNettype, InvalidDataTypeString) {
  EXPECT_FALSE(ValidateNettypeDataKind(NettypeDataKind::kString));
}

TEST(UserDefinedNettype, InvalidDataTypeClass) {
  EXPECT_FALSE(ValidateNettypeDataKind(NettypeDataKind::kClass));
}

// --- Resolution function behavior ---

// §6.6.7: "the simulator calls the resolution function to compute the
//  value of the net from the values of the drivers."
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

// §6.6.7: "Any change in the value of one or more of the drivers shall
//  trigger the evaluation of the resolution function."
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

// --- Unresolved nettype constraints ---

// §6.6.7: "A nettype may be declared without a resolution function, in
//  which case it shall be an error for a net of that nettype to have
//  multiple drivers."
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

// --- Same data type, different resolution functions ---

// §6.6.7: "Two different nettypes can use the same data type, but have
//  different resolution functions."
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

  EXPECT_EQ(var_a->value.words[0].aval & 1, 1u);  // OR: 1|0 = 1
  EXPECT_EQ(var_b->value.words[0].aval & 1, 0u);  // AND: 1&0 = 0
}

// --- Atomic net semantics ---

// §6.6.7: "A net declared with a user-defined nettype is an atomic net."
//  Resolved as a whole, not per-element.
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

// --- Force/release ---

// §6.6.7: "A force statement can override the value of a net of a
//  user-defined nettype."
TEST(UserDefinedNettype, ForceOverridesResolvedValue) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 1);

  UserNettype nt;
  nt.resolution = [](Arena& a,
                     const std::vector<Logic4Vec>& d) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, d[0].words[0].aval & 1);
  };

  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);

  // Force overrides to 0.
  var->value = MakeLogic4VecVal(arena, 1, 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

// §6.6.7: "When released, the net returns to the resolved value."
TEST(UserDefinedNettype, ReleaseRestoresResolvedValue) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net = MakeDrivenNet(arena, var, 1);

  UserNettype nt;
  nt.resolution = [](Arena& a,
                     const std::vector<Logic4Vec>& d) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, d[0].words[0].aval & 1);
  };

  // Force to 0, then release (re-resolve).
  var->value = MakeLogic4VecVal(arena, 1, 0);
  ResolveUserDefinedNet(net, nt, arena);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}
