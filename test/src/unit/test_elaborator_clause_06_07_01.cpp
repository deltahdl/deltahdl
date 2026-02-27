// §6.7.1: Net declarations with built-in net types

#include <gtest/gtest.h>

#include <cstdint>
#include "model_net_declaration.h"

using namespace delta;

namespace {

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

}  // namespace
