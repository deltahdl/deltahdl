

#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
