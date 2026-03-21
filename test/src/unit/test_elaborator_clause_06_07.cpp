#include <gtest/gtest.h>

#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, BasicWireDeclOk) {
  NetDeclInfo info;
  info.type = NetType::kWire;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnTriregIsValid) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, TriregWithChargeStrengthLargeOk) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  info.charge = LocalChargeStrength::kLarge;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnTriIsError) {
  NetDeclInfo info;
  info.type = NetType::kTri;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
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

TEST(NetDecl, ChargeStrengthOnTri0IsError) {
  NetDeclInfo info;
  info.type = NetType::kTri0;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnTri1IsError) {
  NetDeclInfo info;
  info.type = NetType::kTri1;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnSupply0IsError) {
  NetDeclInfo info;
  info.type = NetType::kSupply0;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnSupply1IsError) {
  NetDeclInfo info;
  info.type = NetType::kSupply1;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnTriandIsError) {
  NetDeclInfo info;
  info.type = NetType::kTriand;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnTriorIsError) {
  NetDeclInfo info;
  info.type = NetType::kTrior;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnUwireIsError) {
  NetDeclInfo info;
  info.type = NetType::kUwire;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnWorIsError) {
  NetDeclInfo info;
  info.type = NetType::kWor;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, TriregWithChargeStrengthSmallOk) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  info.charge = LocalChargeStrength::kSmall;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, TriregWithChargeStrengthMediumOk) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  info.charge = LocalChargeStrength::kMedium;
  EXPECT_TRUE(ValidateNetDecl(info));
}

}  // namespace
