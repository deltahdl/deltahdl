#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.3 states as prose that a chandle may not be a member of an untagged
// union; §7.3.2 states the obligation ("Dynamic types and chandle types shall
// not be used in untagged unions"), so the report names §7.3.2.
TEST(UnionDeclarationValidation, ChandleInUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { chandle c; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle type can only be used in tagged unions", 2,
                            "7.3.2"));
}

// What the packed keyword adds is a second, independent rule: §7.2.1 admits
// only packed data types as members, and a chandle is not one. That rule is
// what this case names, since it is what distinguishes the source from
// ChandleInUnpackedUnion_Rejected above (the §7.3.2 report fires here too,
// the union being untagged as well).
TEST(UnionDeclarationValidation, ChandleInPackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { chandle c; logic [63:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type of member 'c' is not allowed in a packed "
                            "union",
                            2, "7.2.1"));
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

// The void-member rule is §7.2's ("A void member is only allowed in tagged
// unions"), not §7.3's, so the report names §7.2 at both positions below.
TEST(UnionDeclarationValidation, VoidMemberInUnpackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { void v; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

TEST(UnionDeclarationValidation, VoidMemberInPackedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { void v; logic [7:0] a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

// §7.2 confines the rand and randc qualifiers to unpacked structures, and that
// is the rule a random qualifier in a union breaks; §7.3 states nothing about
// random qualifiers.
TEST(UnionDeclarationValidation, RandInUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { rand int a; int b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random qualifier is only allowed in unpacked "
                            "structures",
                            2, "7.2"));
}

TEST(UnionDeclarationValidation, RandcInUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { randc int a; int b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random qualifier is only allowed in unpacked "
                            "structures",
                            2, "7.2"));
}

TEST(UnionDeclarationValidation, StringInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { string s; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string type can only be used in tagged unions", 2,
                            "7.3.2"));
}

TEST(UnionDeclarationValidation, RandInTaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { rand int A; int B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "random qualifier is only allowed in unpacked "
                            "structures",
                            2, "7.2"));
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

// Footnote 17 to Syntax 7-1 in §7.2 is what requires the packed (or soft)
// keyword beside a packed dimension, so the report names §7.2 rather than the
// union clause.
TEST(UnionDeclarationValidation, PackedDimOnPlainUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { logic [7:0] a; logic [7:0] b; } [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension on union requires the packed "
                            "keyword",
                            2, "7.2"));
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
  // An event is a handle-like dynamic type, so like chandle and string it may
  // only appear as a member of a tagged union. In an untagged union it must be
  // rejected -- without a tag a sibling member could reinterpret its bits. The
  // obligation is §7.3.2's, not §7.3's, so the report names §7.3.2.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { event e; int a; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event type can only be used in tagged unions", 2,
                            "7.3.2"));
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
