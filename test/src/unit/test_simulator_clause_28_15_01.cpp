// §28.15.1: tri0 and tri1 net strengths

// --- Local types for net type strengths (§28.15) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

// =============================================================
// §28.15.1: tri0 and tri1 net strengths
// =============================================================
// §28.15.1: "The tri0 net type models a net connected to a resistive
//  pulldown device. In the absence of an overriding source, such a
//  signal shall have a value 0 and a pull strength."
TEST(NetStrengths, Tri0DefaultValueIsZero) {
  auto info = GetNetDefault(NetKind::kTri0);
  EXPECT_EQ(info.value, Val4::kV0);
}

TEST(NetStrengths, Tri0DefaultStrengthIsPull) {
  auto info = GetNetDefault(NetKind::kTri0);
  EXPECT_EQ(info.strength, StrengthLevel::kPull);
}

// §28.15.1: "The tri1 net type models a net connected to a resistive
//  pullup device. In the absence of an overriding source, such a
//  signal shall have a value 1 and a pull strength."
TEST(NetStrengths, Tri1DefaultValueIsOne) {
  auto info = GetNetDefault(NetKind::kTri1);
  EXPECT_EQ(info.value, Val4::kV1);
}

TEST(NetStrengths, Tri1DefaultStrengthIsPull) {
  auto info = GetNetDefault(NetKind::kTri1);
  EXPECT_EQ(info.strength, StrengthLevel::kPull);
}

}  // namespace
