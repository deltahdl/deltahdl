#include <gtest/gtest.h>

#include "model_net_default.h"

namespace {

TEST(NetStrengths, Tri0DefaultValueIsZero) {
  auto info = GetNetDefault(NetKind::kTri0);
  EXPECT_EQ(info.value, Val4::kV0);
}

TEST(NetStrengths, Tri0DefaultStrengthIsPull) {
  auto info = GetNetDefault(NetKind::kTri0);
  EXPECT_EQ(info.strength, StrengthLevel::kPull);
}

TEST(NetStrengths, Tri1DefaultValueIsOne) {
  auto info = GetNetDefault(NetKind::kTri1);
  EXPECT_EQ(info.value, Val4::kV1);
}

TEST(NetStrengths, Tri1DefaultStrengthIsPull) {
  auto info = GetNetDefault(NetKind::kTri1);
  EXPECT_EQ(info.strength, StrengthLevel::kPull);
}

}
