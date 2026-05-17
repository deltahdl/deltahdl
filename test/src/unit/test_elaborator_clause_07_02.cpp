#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StructDeclarationValidation, VoidMemberInUnpackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { void v; int a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, VoidMemberInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { void v; logic [7:0] a; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { rand logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandcInPackedStruct_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { randc bit [3:0] x; bit [3:0] y; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandInUnpackedStruct_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { rand int a; int b; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StructDeclarationValidation, RandcInUnpackedStruct_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { randc bit [7:0] x; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2: "Unpacked structures can contain any data type." A packed struct
// is restricted to packed/integer types (§7.2.1), but an unpacked struct
// must accept arbitrary types — including reals, strings, dynamic-sized
// 4-state vectors, and arrays — in the same declaration body.
TEST(StructDeclarationValidation, UnpackedStructAcceptsAnyDataType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct {\n"
      "    real r;\n"
      "    string s;\n"
      "    logic [31:0] v;\n"
      "    byte arr [4];\n"
      "    int i;\n"
      "  } mixed;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2 footnote 20: positive counterpart of the void-member rule — `void`
// is legal as a struct_union_member type within a tagged union. The
// existing negative tests reject void in (un)packed structs; this test
// pins the legal home of the form so the rule fires only on the disallowed
// containers.
TEST(StructDeclarationValidation, VoidMemberInTaggedUnion_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union tagged { void v; int a; } u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2 footnote 17: the union half of the rule allows `soft` as well as
// `packed` to license a trailing packed dimension. The §6.8 elaborator
// file already covers the packed-struct and packed-union variants; this
// test pins the §7.2-specific soft-union variant.
TEST(StructDeclarationValidation, SoftUnionWithPackedDim_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [7:0] b; } [3:0] u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2: "By default, structures are unpacked." A struct with no `packed`
// keyword and a `real` member must elaborate cleanly — real is forbidden
// in a packed struct (§7.2.1 restricts packed members to packed/integer
// types), so the absence of an error proves the elaborator classified the
// declaration as unpacked. If the default were packed, ValidatePackedStruct
// MemberTypes would reject the real member.
TEST(StructDeclarationValidation, BareStructWithRealMemberClassifiedUnpacked) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct { real voltage; int count; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
