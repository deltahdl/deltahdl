#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PackedUnionValidation, HardPackedUnion_SameWidth_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, HardPackedUnion_DifferentWidth_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, PackedUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { real r; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, PackedUnionStringMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { string s; logic [7:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, PackedUnionIntegralMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [31:0] word; logic [3:0][7:0] bytes; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, SoftPackedUnionIntegralMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft packed { bit [7:0] a; bit [3:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, PackedUnionChandleMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { chandle c; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, SoftWithoutPackedKeyword_ValidatedAsPacked) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, SoftUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { real r; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.3.1 (integral-only, §6.11.1): shortreal is a non-integral real-family type
// distinct from `real`, and it must also be rejected as a packed-union member.
TEST(PackedUnionValidation, PackedUnionShortrealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { shortreal r; logic [31:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.3.1 (integral-only, §6.11.1): the remaining predefined integral kinds
// (byte/shortint/integer/time) are admissible packed-union members. Their sizes
// differ, so the union is soft packed and its width is the largest (time = 64).
TEST(PackedUnionValidation, SoftPackedUnionPredefinedIntegralKinds_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { byte b; shortint s; integer i; time t; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 64u);
}

// §7.3.1: a union mixing a 4-state member with a 2-state member is 4-state.
// This exercises the 4-state `integer` kind (distinct from `logic`) against
// 2-state `int`; both are 32 bits, so the hard-packed same-size rule is
// satisfied.
TEST(PackedUnionValidation, MixedStateIntegerAndInt_UnionIs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { integer a; int b; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_4state);
}

TEST(PackedUnionValidation, NestedPackedStructInPackedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed {\n"
      "    struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "    logic [7:0] flat;\n"
      "  } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, EnumMemberInPackedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [7:0] { A = 0, B = 1 } my_enum;\n"
      "  union packed { my_enum e; logic [7:0] raw; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, HardPackedThreeMembers_ThirdDiffers_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; logic [3:0] c; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedUnionValidation, MixedStateMembers_UnionIs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_4state);
}

TEST(PackedUnionValidation, AllTwoStateMembers_UnionIs2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { bit [7:0] a; bit [7:0] b; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_FALSE(vars[0].is_4state);
}

TEST(PackedUnionValidation, SoftPackedUnion_WidthIsMaxOfMembers) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { bit [7:0] narrow; bit [23:0] wide; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 24u);
}

TEST(PackedUnionValidation,
     SoftPackedUnion_PredefinedIntegralKinds_WidthIsLongest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed { bit [3:0] tiny; int mid; longint widest; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 64u);
}

TEST(PackedUnionValidation, NestedSoftPackedUnion_WidthRecursesToOuterMax) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft packed {\n"
      "    bit [3:0] tiny;\n"
      "    union soft packed { bit [11:0] inner_wide; bit [5:0] inner_narrow; "
      "} "
      "nested;\n"
      "  } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].width, 12u);
}

}  // namespace
