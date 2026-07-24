#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

// §28.15.2: the user names the specific charge strength in the net declaration.
// The (large) form carries through elaboration onto the net, distinct from both
// the small case above and the medium default.
TEST(TriregElaboration, ChargeStrengthLarge) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) g;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kLarge);
}

// §28.15.2: medium is also the value a user may name explicitly. Writing
// (medium) in the declaration must reach the net through the same declared-
// strength path that carries small and large -- not merely coincide with the
// defaulted value of a bare trireg -- so the third admitted keyword is
// exercised as an explicit input form rather than only as the default.
TEST(TriregElaboration, ChargeStrengthMediumExplicit) {
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

}  // namespace
