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

TEST(PackedUnionValidation, SoftPackedUnion_DifferentWidth_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
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

// §7.3.1: soft without packed keyword — treated as packed for validation.
TEST(PackedUnionValidation, SoftWithoutPackedKeyword_ValidatedAsPacked) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.1: soft union still requires integral member types.
TEST(PackedUnionValidation, SoftUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { real r; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.3.1: nested packed struct inside packed union is integral — allowed.
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

// §7.3.1: enum member in packed union — integral type, allowed.
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

// §7.3.1: hard packed union with three members, all same width — OK.
TEST(PackedUnionValidation, HardPackedThreeMembers_SameWidth_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; logic [7:0] c; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.3.1: hard packed union — third member differs in width.
TEST(PackedUnionValidation, HardPackedThreeMembers_ThirdDiffers_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; logic [3:0] c; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
