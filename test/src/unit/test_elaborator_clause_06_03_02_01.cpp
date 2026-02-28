// §6.3.2.1: Charge strength

#include <gtest/gtest.h>

#include <cstdint>

#include "model_net_declaration.h"

using namespace delta;

namespace {

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

}  // namespace
