#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PackedArrayValidation, PackedDimOnByte_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  byte [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnShortint_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortint [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnInt_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnLongint_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  longint [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnInteger_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  integer [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnTime_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  time [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnLogic_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnBit_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  bit [7:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnReg_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  reg [7:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimElaboratesWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(PackedArrayValidation, XzInPackedDimLeft_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1'bx:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, XzInPackedDimRight_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:1'bz] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, XzInExtraPackedDim_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [3:0][1'bx:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, MultiDimPackedArrayWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0][7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

TEST(PackedArrayValidation, PackedDimOnEnumBaseType_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [1:0] {A, B, C} e_t;\n"
      "  e_t x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
