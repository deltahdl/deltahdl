#include <gtest/gtest.h>

#include "model_net_default.h"

namespace {

TEST(NetStrengths, Supply0HasSupplyStrength) {
  auto info = GetNetDefault(NetKind::kSupply0);
  EXPECT_EQ(info.strength, StrengthLevel::kSupply);
}

TEST(NetStrengths, Supply1HasSupplyStrength) {
  auto info = GetNetDefault(NetKind::kSupply1);
  EXPECT_EQ(info.strength, StrengthLevel::kSupply);
}

TEST(NetStrengths, Supply0ValueIsZero) {
  auto info = GetNetDefault(NetKind::kSupply0);
  EXPECT_EQ(info.value, Val4::kV0);
}

TEST(NetStrengths, Supply1ValueIsOne) {
  auto info = GetNetDefault(NetKind::kSupply1);
  EXPECT_EQ(info.value, Val4::kV1);
}

}
