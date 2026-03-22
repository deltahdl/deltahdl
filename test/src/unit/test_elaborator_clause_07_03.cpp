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

TEST(UnionDeclarationValidation, ChandleInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { chandle Handle; int Value; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
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

// Footnote 20: void member only in tagged unions.
TEST(UnionDeclarationValidation, VoidMemberInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void Invalid; int Valid; } u;\n"
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

// Footnote 20: random_qualifier only in unpacked structures (not unions).
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

// Footnote 17: packed dim on union requires soft/packed keyword.
TEST(UnionDeclarationValidation, PackedDimOnUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { int a; int b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.3: String (dynamic type) in untagged union shall be rejected.
TEST(UnionDeclarationValidation, StringInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { string s; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.3: String (dynamic type) in tagged union is allowed.
TEST(UnionDeclarationValidation, StringInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { string S; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Footnote 20: random_qualifier rejected in tagged unions too (only unpacked structs).
TEST(UnionDeclarationValidation, RandInTaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { rand int A; int B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// Footnote 17: packed dim on union with soft keyword is allowed.
TEST(UnionDeclarationValidation, PackedDimOnSoftUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { int a; logic [31:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Footnote 17: packed dim on packed union is allowed.
TEST(UnionDeclarationValidation, PackedDimOnPackedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
