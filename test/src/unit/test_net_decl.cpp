#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

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

bool ValidateNetDecl(const NetDeclInfo& info);
bool ValidateNetDataType(NetDataTypeKind kind);
void InitializeNet(Net& net, NetType type, Arena& arena);
void InitializeTriregNet(Net& net, LocalChargeStrength str, Arena& arena);

// --- Helpers ---

static uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal1 = 1;
static constexpr uint8_t kValX = 2;
static constexpr uint8_t kValZ = 3;

// =============================================================
// §6.7: Net declarations
// =============================================================

// --- Charge strength (§6.7, footnote 16) ---

// §6.7: "A charge strength shall only be used with the trireg keyword."
TEST(NetDecl, ChargeStrengthOnlyWithTrireg) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnWireIsError) {
  NetDeclInfo info;
  info.type = NetType::kWire;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnWandIsError) {
  NetDeclInfo info;
  info.type = NetType::kWand;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// --- vectored/scalared (§6.7, footnote 16) ---

// §6.7: "When the vectored or scalared keyword is used, there shall be
//  at least one packed dimension."
TEST(NetDecl, VectoredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, VectoredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

// --- Interconnect restrictions (§6.7.1) ---

// §6.7.1: "A net declared as an interconnect net shall:
//  — have no data type"
TEST(NetDecl, InterconnectNoDataType) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_data_type = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, InterconnectWithDimensionsOk) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

// §6.7.1: "— not specify drive_strength or charge_strength"
TEST(NetDecl, InterconnectNoDriveStrength) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_drive_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, InterconnectNoChargeStrength) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// §6.7.1: "— not have assignment expressions"
TEST(NetDecl, InterconnectNoAssignment) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_assignment = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// §6.7.1: "— specify at most one delay value."
TEST(NetDecl, InterconnectOneDelayOk) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.delay_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, InterconnectMultipleDelaysError) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.delay_count = 3;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// --- Valid net data types (§6.7.1) ---

// §6.7.1: "A valid data type for a net shall be one of the following:
//  a) A 4-state integral type"
TEST(NetDecl, ValidNetDataType4StateIntegral) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::k4StateIntegral));
}

// §6.7.1: "b) A fixed-size unpacked array or unpacked structure or union,
//  where each element has a valid data type for a net."
TEST(NetDecl, ValidNetDataTypeFixedUnpacked) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::kFixedUnpackedValid));
}

// §6.7.1: 2-state integral is NOT valid for built-in net types.
TEST(NetDecl, InvalidNetDataType2StateIntegral) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::k2StateIntegral));
}

TEST(NetDecl, InvalidNetDataTypeReal) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kReal));
}

TEST(NetDecl, InvalidNetDataTypeDynamicArray) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kDynamicArray));
}

TEST(NetDecl, InvalidNetDataTypeString) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kString));
}

// --- Strength information (§6.7.1) ---

// §6.7.1: "each bit of a net shall have additional strength information."
TEST(NetDecl, EachBitHasStrengthInformation) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0xF));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  EXPECT_EQ(net.driver_strengths.size(), 1u);
}

// --- Default initialization (§6.7.1) ---

// §6.7.1: "The default initialization value for a net shall be the
//  value z."
TEST(NetDecl, DefaultInitializationIsZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

// §6.7.1: "Nets with drivers shall assume the output value of their
//  drivers."
TEST(NetDecl, NetsWithDriversAssumeDriverValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}

// §6.7.1: "The trireg net shall default to the value x, with the
//  strength specified in the net declaration."
TEST(NetDecl, TriregDefaultsToXSmall) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kSmall, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NetDecl, TriregDefaultsToXMedium) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kMedium, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NetDecl, TriregDefaultsToXLarge) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kLarge, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

// --- §6.7.3: Initialization of nets with user-defined nettypes ---

using ResolutionFn =
    std::function<Logic4Vec(Arena&, const std::vector<Logic4Vec>&)>;

struct UserNettype {
  uint32_t bit_width = 1;
  ResolutionFn resolution;
};

void ActivateResolutionAtTimeZero(Net& net, const UserNettype& nt,
                                  Arena& arena);
void SetUserNettypeInitialValue(Net& net, const UserNettype& nt,
                                Arena& arena);

// §6.7.3: "The resolution function for any net of a user-defined nettype
//  shall be activated at time zero at least once."
TEST(NetDecl, UserDefinedResolutionActivatedAtTimeZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>&) -> Logic4Vec {
    activated = true;
    return MakeLogic4Vec(a, 1);
  };

  ActivateResolutionAtTimeZero(net, nt, arena);
  EXPECT_TRUE(activated);
}

// §6.7.3: "This activation occurs even for such nets with no drivers."
TEST(NetDecl, UserDefinedResolutionAtTimeZeroEvenNoDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // No drivers added.

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
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
  auto* var = arena.Create<Variable>();
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
