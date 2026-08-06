#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DriveStrengthElaboration, DriveStrengthOnVectorNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign (strong0, weak1) w = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarNetIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, SupplyNetTypeHasNoStrengthError) {
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

TEST(DriveStrengthElaboration, NetDeclStrengthOnScalarIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, NetDeclStrengthOnVectorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) [3:0] w = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarVariableIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign (strong0, weak1) v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(DriveStrengthElaboration, DriveStrengthPropagatedToImplicitContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (supply0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

TEST(DriveStrengthElaboration, Supply1VectorNetTypeHasNoStrengthError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply1 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §10.3.4: the strength pairs (highz1, highz0) and (highz0, highz1) shall be
// treated as illegal constructs. The parser accepts the syntax (both slots
// encode to the highz level); the elaborator rejects an all-highz drive
// strength on a continuous assignment.
TEST(DriveStrengthElaboration, Highz0Highz1ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The order of the two strengths is arbitrary, so the reversed all-highz pair
// is equally illegal.
TEST(DriveStrengthElaboration, Highz1Highz0ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same prohibition applies when the all-highz strength is written on a net
// declaration assignment.
TEST(DriveStrengthElaboration, Highz0Highz1NetDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, MultipleAssignsPreserveIndependentStrengths) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (supply0, supply1) a = 1'b1;\n"
      "  assign (weak0, weak1) b = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
  EXPECT_EQ(mod->assigns[1].drive_strength0, 2u);
  EXPECT_EQ(mod->assigns[1].drive_strength1, 2u);
}

}  // namespace
