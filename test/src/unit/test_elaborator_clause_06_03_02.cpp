#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, ChargeStrengthOnlyWithTrireg) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, TriregWithChargeStrengthOk) {
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

TEST(Elaborator, DriveStrengthOnNetDeclWithAssignOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaborator, DriveStrengthOnNetDeclWithoutAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
