

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

}  // namespace
