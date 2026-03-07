// Non-LRM tests

#include <gtest/gtest.h>
#include "fixture_elaborator.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, ChargeStrengthOnTriIsError) {
  NetDeclInfo info;
  info.type = NetType::kTri;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnTriregIsValid) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
}

// §6.3.2.1: trireg without explicit charge strength defaults to kMedium.
TEST(Elaborator, TriregDefaultChargeStrengthMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "a") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
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
