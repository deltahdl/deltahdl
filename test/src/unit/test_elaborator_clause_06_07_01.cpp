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

// §6.7.2: User-defined nettype produces a net in elaboration.
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
  // The user-defined nettype decl should produce a net, not a variable.
  bool found_net = false;
  for (auto& net : mod->nets) {
    if (net.name == "t.x") found_net = true;
  }
  EXPECT_TRUE(found_net);
}

// §6.7.2: Array of user-defined nettype.
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

// §6.3.2.1: trireg with explicit (small) charge strength.
TEST(Elaborator, TriregExplicitChargeStrengthSmall) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (small) s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "s") {
      EXPECT_EQ(net.charge_strength, Strength::kSmall);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §6.3.2.1: trireg with explicit (large) charge strength.
TEST(Elaborator, TriregExplicitChargeStrengthLarge) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (large) l;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "l") {
      EXPECT_EQ(net.charge_strength, Strength::kLarge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §6.3.2.1: trireg with explicit (medium) charge strength.
TEST(Elaborator, TriregExplicitChargeStrengthMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (medium) m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "m") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
