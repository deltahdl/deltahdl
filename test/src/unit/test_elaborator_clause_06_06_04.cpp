#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TriregElaboration, TriregNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg tg;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTrireg);
}

TEST(TriregElaboration, DefaultChargeStrengthIsMedium) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg tg;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kMedium);
}

TEST(TriregElaboration, ChargeStrengthSmall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (small) s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kSmall);
}

TEST(TriregElaboration, ChargeStrengthMedium) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (medium) m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kMedium);
}

TEST(TriregElaboration, ChargeStrengthLarge) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) lg;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kLarge);
}

TEST(TriregElaboration, TriregIsNetNotVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg tg;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_TRUE(mod->variables.empty());
}

}  // namespace
