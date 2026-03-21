#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

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

TEST(NetDecl, InterconnectNoAssignment) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_assignment = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

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

TEST(NetDecl, ValidNetDataType4StateIntegral) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::k4StateIntegral));
}

TEST(NetDecl, ValidNetDataTypeFixedUnpacked) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::kFixedUnpackedValid));
}

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

TEST(NetDecl, UserDefinedNettypeCreatesNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];

  bool found_net = false;
  for (auto& net : mod->nets) {
    if (net.name == "x") found_net = true;
  }
  EXPECT_TRUE(found_net);
}

TEST(NetDecl, UserDefinedNettypeArrayCreatesNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic mynet;\n"
      "  mynet x [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetDecl, ChargeStrengthOnTriregIsValid) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, VectoredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

}  // namespace
