#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- drive_strength elaboration ---

TEST(StrengthElaboration, DriveStrengthPreservedInContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 4u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 2u);
}

TEST(StrengthElaboration, DriveStrengthReversedOrderPreserved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 3u);
}

TEST(StrengthElaboration, DriveStrengthHighz0WithStrength1) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, supply1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(StrengthElaboration, DriveStrengthHighz1WithStrength0) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, weak0) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 2u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 1u);
}

TEST(StrengthElaboration, DefaultDriveStrengthIsZero) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 0u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 0u);
}

TEST(StrengthElaboration, Highz0Highz1IsError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(StrengthElaboration, Highz1Highz0IsError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// --- charge_strength elaboration ---

TEST(StrengthElaboration, ChargeStrengthSmallOnTrireg) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  trireg (small) t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kSmall);
}

TEST(StrengthElaboration, ChargeStrengthMediumOnTrireg) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  trireg (medium) t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kMedium);
}

TEST(StrengthElaboration, ChargeStrengthLargeOnTrireg) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  trireg (large) t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kLarge);
}

TEST(StrengthElaboration, TriregDefaultChargeStrengthMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  trireg t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].charge_strength, Strength::kMedium);
}

// --- drive_strength on net declaration ---

TEST(StrengthElaboration, NetDeclDriveStrengthPreserved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire (supply0, supply1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(StrengthElaboration, NetDeclDriveStrengthWithoutAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire (strong0, weak1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
