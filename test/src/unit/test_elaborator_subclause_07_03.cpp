#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(UnionDeclarationValidation, DynamicMembersOfAnUntaggedUnionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef chandle h_t;\n"
      "  union { int d[]; int i; } a;\n"
      "  union { int q[$]; int i; } b;\n"
      "  union { int m[string]; int i; } c;\n"
      "  union tagged { int q[$]; int i; } t;\n"
      "  union { h_t h; int i; } th;\n"
      "  union { int f[2]; int i; } fixed;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "member 'd' can only be used in tagged", 3,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'q' can only be used in tagged", 4,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'm' can only be used in tagged", 5,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(
      diags, "chandle type can only be used in tagged unions", 7, "7.3.2"));
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 6u) << d.message;
    EXPECT_NE(d.loc.line, 8u) << d.message;
  }
}

TEST(UnionDeclarationValidation, DynamicAndChandleMembersReportedInEveryPlace) {
  std::string src =
      "typedef union {int d []; int i;} cu_t;\n"
      "package pk; typedef union {int q [$]; int i;} pu_t; endpackage\n"
      "interface I; union {chandle h; int i;} a; endinterface\n"
      "checker ck; union {int q [$]; int i;} d; endchecker\n"
      "program P; union {string s; int i;} c; endprogram\n"
      "module t;\n"
      "  I ii(); ck c1(); P pp();\n"
      "  class C; union {chandle h; int i;} cu; endclass\n"
      "  function automatic void f(); union {int m [int]; int i;} u; "
      "endfunction\n"
      "  if (1) begin : g union {string s; int i;} gu; end\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "member 'd' can only be used in tagged", 1,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'q' can only be used in tagged", 2,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "chandle type can only be used in tagged", 3,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'q' can only be used in tagged", 4,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "string type can only be used in tagged", 5,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "chandle type can only be used in tagged", 8,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'm' can only be used in tagged", 9,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "string type can only be used in tagged", 10,
                            "7.3.2"));
}

TEST(UnionDeclarationValidation,
     DISABLED_TypedefOfADynamicArrayQueueOrAssociativeArrayIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int da_t []; typedef int qq_t [$]; typedef int aa_t "
      "[string];\n"
      "  union {da_t d; int i;} a;\n"
      "  union {qq_t q; int i;} b;\n"
      "  union {aa_t m; int i;} c;\n"
      "  union tagged {da_t d; qq_t q; aa_t m; int i;} ok;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "member 'd' can only be used in tagged", 3,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'q' can only be used in tagged", 4,
                            "7.3.2"));
  EXPECT_TRUE(ReportedError(diags, "member 'm' can only be used in tagged", 5,
                            "7.3.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(UnionDeclarationValidation,
     TaggedUnionAcceptsEveryDynamicAndChandleMember) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  union tagged {int d []; int q [$]; int m [string]; chandle h;\n"
      "                string s; int i;} ok;\n"
      "  class C; union tagged {int d []; chandle h; int i;} cu; endclass\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
