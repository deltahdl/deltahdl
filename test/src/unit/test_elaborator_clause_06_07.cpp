// §6.7: Net declarations

#include <gtest/gtest.h>

#include <cstdint>

#include "model_net_declaration.h"

using namespace delta;

namespace {

// =============================================================
// §6.7: Net declarations
// =============================================================
// --- Charge strength (§6.7, footnote 16) ---
// §6.7:
TEST(NetDecl, ChargeStrengthOnlyWithTrireg) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
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

TEST(NetDecl, ScalaredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

}  // namespace
