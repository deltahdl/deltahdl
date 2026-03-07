#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause1003, Validate_IllegalDriveStrengthHighz0Highz1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1003, Validate_IllegalDriveStrengthHighz1Highz0) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1003, Validate_LegalDriveStrengthHighz0Strong1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §10.3.4: Drive strength applies only to scalar nets.

TEST(ElabClause100304, DriveStrengthOnVectorNet_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign (strong0, weak1) w = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause100304, DriveStrengthOnScalarNet_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §10.3.4: Exception — supply0/supply1 nets are excluded from scalar-only rule.

TEST(ElabClause100304, DriveStrengthOnSupply0Net_NoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply0 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §10.3.4: Default strength is (strong1, strong0) — stored as 0 in RTLIR.

TEST(ElabClause100304, DefaultStrengthIsZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 0u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 0u);
}

// §10.3.4: Strength values are preserved in RTLIR.

TEST(ElabClause100304, StrengthPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull0, supply1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 3u);  // pull0
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);  // supply1
}

// §10.3.4: Net declaration with drive strength on scalar net.

TEST(ElabClause100304, NetDeclStrengthScalar_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabClause100304, NetDeclStrengthVector_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) [3:0] w = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.3.2.2: Continuous assignment without drive strength has defaults (0, 0).
TEST(Elaborator, ContAssignNoDriveStrengthDefault) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
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

// §6.3.2.2: Drive strength (highz1, highz0) — reversed order, also illegal.
TEST(Elaborator, DriveStrengthHighz1Highz0IsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.3.2.2: Drive strength supply0, supply1 is valid.
TEST(Elaborator, DriveStrengthSupply0Supply1Valid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);  // supply0
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);  // supply1
}

}  // namespace
