#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §28.15.2 R4: if the user omits the charge strength on a trireg declaration,
// the net's charge strength must default to medium. Verifies the AST→Net
// plumbing picks up the default when no `(small|medium|large)` is given.
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

// §28.15.2 R3 (small): a user-declared `(small)` strength must reach the
// simulator net unchanged.
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

// §28.15.2 R3 (medium): explicit `(medium)` must also reach the net — the
// default-medium rule must not mask an explicit specification.
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

// §28.15.2 R3 (large): `(large)` must reach the net. Together with the small
// and medium cases this covers the complete set of permitted values.
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

}  // namespace
