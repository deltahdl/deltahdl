#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ContinuousAssignmentElaboration, Validate_IllegalDriveStrengthHighz0Highz1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ContinuousAssignmentElaboration, Validate_IllegalDriveStrengthHighz1Highz0) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ContinuousAssignmentElaboration, Validate_LegalDriveStrengthHighz0Strong1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DriveStrengthOnVectorNet_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign (strong0, weak1) w = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarNet_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DriveStrengthOnSupply0Net_NoError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply0 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DefaultStrengthIsZero) {
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

TEST(DriveStrengthElaboration, StrengthPreservedInRtlir) {
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
  EXPECT_EQ(mod->assigns[0].drive_strength0, 3u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(DriveStrengthElaboration, NetDeclStrengthScalar_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, NetDeclStrengthVector_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) [3:0] w = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

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
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(Elaborator, DriveStrengthHighz0Strong1Valid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

TEST(Elaborator, DriveStrengthOnContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 4u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 2u);
}

}  // namespace
