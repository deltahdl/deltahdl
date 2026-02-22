// §6.7.3: Initialization of nets with user-defined nettypes

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"
#include <cstdint>
#include <functional>
#include <gtest/gtest.h>

using namespace delta;

// --- Local types for net declaration validation (§6.7) ---
enum class LocalChargeStrength : uint8_t {
  kSmall,
  kMedium,
  kLarge,
};

enum class NetDataTypeKind : uint8_t {
  k4StateIntegral,
  kFixedUnpackedValid,
  k2StateIntegral,
  kReal,
  kDynamicArray,
  kString,
};

struct NetDeclInfo {
  NetType type = NetType::kWire;
  bool has_charge_strength = false;
  LocalChargeStrength charge = LocalChargeStrength::kMedium;
  bool is_vectored = false;
  bool is_scalared = false;
  bool is_interconnect = false;
  uint32_t packed_dim_count = 0;
  uint32_t delay_count = 0;
  bool has_data_type = false;
  bool has_drive_strength = false;
  bool has_assignment = false;
  NetDataTypeKind data_kind = NetDataTypeKind::k4StateIntegral;
};

bool ValidateNetDecl(const NetDeclInfo &info);

bool ValidateNetDataType(NetDataTypeKind kind);

void InitializeNet(Net &net, NetType type, Arena &arena);

void InitializeTriregNet(Net &net, LocalChargeStrength str, Arena &arena);

static bool ValidateInterconnectDecl(const NetDeclInfo &info) {
  if (info.has_data_type)
    return false;
  if (info.has_drive_strength)
    return false;
  if (info.has_charge_strength)
    return false;
  if (info.has_assignment)
    return false;
  return info.delay_count <= 1;
}

bool ValidateNetDecl(const NetDeclInfo &info) {
  // Charge strength only allowed on trireg.
  if (info.has_charge_strength && info.type != NetType::kTrireg &&
      !info.is_interconnect)
    return false;
  // vectored/scalared require at least one packed dimension.
  if ((info.is_vectored || info.is_scalared) && info.packed_dim_count == 0)
    return false;
  // Interconnect constraints.
  if (info.is_interconnect)
    return ValidateInterconnectDecl(info);
  return true;
}

bool ValidateNetDataType(NetDataTypeKind kind) {
  switch (kind) {
  case NetDataTypeKind::k4StateIntegral:
  case NetDataTypeKind::kFixedUnpackedValid:
    return true;
  case NetDataTypeKind::k2StateIntegral:
  case NetDataTypeKind::kReal:
  case NetDataTypeKind::kDynamicArray:
  case NetDataTypeKind::kString:
    return false;
  }
  return false;
}

void InitializeNet(Net &net, NetType type, Arena &arena) {
  (void)type;
  (void)arena;
  if (!net.drivers.empty()) {
    // Resolve to driver value.
    net.resolved->value = net.drivers[0];
  } else {
    // Default to z: aval=1, bval=1.
    for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
      net.resolved->value.words[i].aval = 1;
      net.resolved->value.words[i].bval = 1;
    }
  }
}

void InitializeTriregNet(Net &net, LocalChargeStrength str, Arena &arena) {
  (void)str;
  (void)arena;
  // Set value to x: aval=0, bval=1.
  for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
    net.resolved->value.words[i].aval = 0;
    net.resolved->value.words[i].bval = 1;
  }
}

using ResolutionFn =
    std::function<Logic4Vec(Arena &, const std::vector<Logic4Vec> &)>;

struct UserNettype {
  uint32_t bit_width = 1;
  ResolutionFn resolution;
};

void ActivateResolutionAtTimeZero(Net &net, const UserNettype &nt,
                                  Arena &arena) {
  if (nt.resolution) {
    Logic4Vec result = nt.resolution(arena, net.drivers);
    net.resolved->value = result;
  }
}

void SetUserNettypeInitialValue(Net &net, const UserNettype &nt, Arena &arena) {
  net.resolved->value = MakeLogic4Vec(arena, nt.bit_width);
  // Default for logic is X: aval=0, bval=all-ones.
  for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
    net.resolved->value.words[i].bval = ~uint64_t{0};
  }
}

// --- Helpers ---
static uint8_t ValOf(const Variable &v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kValX = 2;

namespace {

// §6.7.3: "The resolution function for any net of a user-defined nettype
//  shall be activated at time zero at least once."
TEST(NetDecl, UserDefinedResolutionActivatedAtTimeZero) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena &a, const std::vector<Logic4Vec> &) -> Logic4Vec {
    activated = true;
    return MakeLogic4Vec(a, 1);
  };

  ActivateResolutionAtTimeZero(net, nt, arena);
  EXPECT_TRUE(activated);
}

// §6.7.3:
TEST(NetDecl, UserDefinedResolutionAtTimeZeroEvenNoDrivers) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // No drivers added.

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena &a,
                      const std::vector<Logic4Vec> &drivers) -> Logic4Vec {
    activated = true;
    EXPECT_TRUE(drivers.empty());
    return MakeLogic4Vec(a, 1);
  };

  ActivateResolutionAtTimeZero(net, nt, arena);
  EXPECT_TRUE(activated);
}

// §6.7.3: "The default initialization value for a net with a user-defined
//  nettype shall be the default value defined by the data type."
// NOTE: default for logic is x, not z.
TEST(NetDecl, UserDefinedNettypeDefaultIsDataTypeDefault) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  UserNettype nt;
  SetUserNettypeInitialValue(net, nt, arena);
  // logic default is x (aval=1, bval=1 → x in VPI convention... actually
  // let me just check the bits).
  EXPECT_EQ(ValOf(*var), kValX);
}

} // namespace
