#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UnionDeclarationValidation, ChandleInUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { chandle c; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, ChandleInPackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { chandle c; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, AnonymousUnionInStruct_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {\n"
      "    bit isfloat;\n"
      "    union { int i; shortreal f; } n;\n"
      "  } tagged_st;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, UnpackedUnionBasic_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union { int i; shortreal f; } num;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, VoidMemberInUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { void v; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, VoidMemberInPackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { void v; logic [7:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, RandInUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { rand int a; int b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, RandcInUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { randc int a; int b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, StringInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { string s; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, RandInTaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { rand int A; int B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, PackedDimOnSoftUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { int a; logic [31:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, PackedDimOnPlainUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { logic [7:0] a; logic [7:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, ChandleInTaggedUnion_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { chandle c; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, StringInTaggedUnion_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { string s; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, EventInUntaggedUnion_Rejected) {
  // §7.3: an event is a handle-like dynamic type, so like chandle and string it
  // may only appear as a member of a tagged union. In an untagged union it must
  // be rejected -- without a tag a sibling member could reinterpret its bits.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { event e; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, EventInTaggedUnion_OK) {
  // §7.3: the same event member is permitted once the union is tagged, since
  // the tag makes a type-safe read of the dynamic handle possible.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { event e; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, PackedDimOnPackedOnlyUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, VoidMemberInTaggedUnion_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void v; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnionDeclarationValidation, UnpackedUnionOfStructsSharingInitial_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { int kind; int a; } pa_t;\n"
      "  typedef struct { int kind; int b; int c; } pb_t;\n"
      "  typedef union { pa_t pa; pb_t pb; } u_t;\n"
      "  u_t u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
