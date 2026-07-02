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

// §7.2: an unpacked structure member may be declared with any data type, which
// includes a user-defined enumeration. UnpackedStructAcceptsAnyDataType above
// exercises real/string/vector/array/int members; an enum member is a distinct
// admitted member type not otherwise observed at the elaborator stage. The
// unpacked struct carries no packed-member-type restriction, so the enum-typed
// member is accepted.
TEST(StructDeclarationValidation, UnpackedStructEnumMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [1:0] { A, B, C } abc_e;\n"
      "  struct { abc_e sel; int payload; } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2: an unpacked structure member may itself be a structure. A nested inline
// (unpacked) struct member is a distinct admitted member type; the parser
// already observes this form, but the elaborator's acceptance of an unpacked
// struct holding a struct-typed member is not otherwise observed here.
TEST(StructDeclarationValidation, UnpackedStructNestedStructMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct {\n"
      "    struct { int x; int y; } point;\n"
      "    int id;\n"
      "  } s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

// §7.2, footnote 17: when a packed dimension follows the struct keyword, the
// packed keyword shall also be used. An unpacked struct carrying a trailing
// packed dimension is illegal. The trailing [3:0] is parsed onto the struct
// type's packed dimension, so the elaborator's packed-dim gate must fire.
TEST(StructDeclarationValidation, PackedDimOnStructWithoutPackedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { logic [7:0] a; logic [7:0] b; } [3:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.2, footnote 17: a packed struct may carry a trailing packed dimension.
// This is the positive discriminator showing the gate opens once packed is
// present; it shares the same validator as the union form below.
TEST(StructDeclarationValidation, PackedDimOnPackedStructAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } [3:0] s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2, footnote 17: when a packed dimension follows the union keyword, the
// soft and/or packed keyword shall also be used. A plain (unpacked) union with
// a trailing packed dimension carries neither, so it is illegal. This weaves
// the same packed-dimension rule across structures and unions.
TEST(StructDeclarationValidation, PackedDimOnPlainUnionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { logic [7:0] a; logic [7:0] b; } [3:0] u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.2, footnote 20: a void member is legal only within a tagged union. A
// plain (non-tagged) union with a void member must be rejected; this
// discriminates the tagged gate from the tagged-union positive case above.
TEST(StructDeclarationValidation, VoidMemberInPlainUnionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { void v; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
