#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

DataType MakePackedTaggedUnion(size_t count) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_tagged = true;
  dt.is_packed = true;
  static const char* const kNames[] = {"M0", "M1", "M2", "M3", "M4",
                                       "M5", "M6", "M7", "M8"};
  for (size_t i = 0; i < count; ++i) {
    StructMember m;
    m.type_kind = DataTypeKind::kInt;
    m.name = kNames[i];
    dt.struct_members.push_back(m);
  }
  return dt;
}

TEST(TaggedUnionPackedRepr, TagWidthCoversAllMemberNames) {
  EXPECT_EQ(EvalTypeWidth(MakePackedTaggedUnion(5)), 35u);
}

TEST(TaggedUnionValidation, ChandleInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { chandle Handle; int Value; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, ChandleInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { chandle Handle; int Value; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle type can only be used in tagged unions", 2,
                            "7.3.2"));
}

TEST(TaggedUnionValidation, VoidMemberInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void Invalid; int Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, StringInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { string S; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, StringInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { string S; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "string type can only be used in tagged unions", 2,
                            "7.3.2"));
}

TEST(TaggedUnionValidation, EventInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { event E; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, EventInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { event E; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event type can only be used in tagged unions", 2,
                            "7.3.2"));
}

TEST(TaggedUnionValidation, PackedTaggedUnionIntegralMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { bit [7:0] A; bit [15:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, PackedTaggedUnionDifferentWidths_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { bit [7:0] Narrow; bit [31:0] Wide; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, PackedTaggedUnionRealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { real R; bit [63:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type of member 'R' is not allowed in a packed union", 2, "7.2.1"));
}

TEST(TaggedUnionPackedRepr, VoidOnlyTaggedUnionHasOnlyTagBits) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_tagged = true;
  dt.is_packed = true;
  StructMember a;
  a.type_kind = DataTypeKind::kVoid;
  a.name = "A";
  StructMember b;
  b.type_kind = DataTypeKind::kVoid;
  b.name = "B";
  dt.struct_members = {a, b};
  EXPECT_EQ(EvalTypeWidth(dt), 1u);
}

TEST(TaggedUnionPackedRepr, TagBitsAreLeftJustified) {
  auto dt = MakePackedTaggedUnion(2);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 1u);
  EXPECT_EQ(TaggedUnionTagBitOffset(dt), 32u);
}

TEST(TaggedUnionPackedRepr, MemberBitsAreRightJustified) {
  auto dt = MakePackedTaggedUnion(5);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 3u);
  EXPECT_EQ(TaggedUnionTagBitOffset(dt), 32u);
}

TEST(TaggedUnionPackedRepr, SingleMemberTaggedUnionHasZeroTagBits) {
  auto dt = MakePackedTaggedUnion(1);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 0u);
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
}

TEST(TaggedUnionPackedRepr, FourMemberTagIsTwoBits) {
  auto dt = MakePackedTaggedUnion(4);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 2u);
  EXPECT_EQ(EvalTypeWidth(dt), 34u);
}

TEST(TaggedUnionPackedRepr, EightMemberTagIsThreeBits) {
  auto dt = MakePackedTaggedUnion(8);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 3u);
  EXPECT_EQ(EvalTypeWidth(dt), 35u);
}

TEST(TaggedUnionPackedRepr, NineMemberTagIsFourBits) {
  auto dt = MakePackedTaggedUnion(9);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 4u);
  EXPECT_EQ(EvalTypeWidth(dt), 36u);
}

TEST(TaggedUnionValidation, TaggedAssignmentInvalidMemberName_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  initial begin\n"
      "    u = tagged Bogus 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'U' has no member named 'Bogus'", 5,
                            "11.9"));
}

TEST(TaggedUnionValidation, PackedTaggedUnionVoidMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { void Invalid; bit [31:0] Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, PackedUntaggedUnionVoidMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { void Invalid; bit [31:0] Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

TEST(TaggedUnionValidation, CuScopeUntaggedUnionVoidMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "typedef union packed { void Invalid; bit [31:0] Valid; } u_t;\n"
      "module top; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 1,
                            "7.2"));
}

TEST(TaggedUnionPackedRepr, PackedTaggedUnionWidthFromRealSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged packed { void Invalid; bit [31:0] Valid; } "
      "VInt;\n"
      "  VInt u;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  auto it = design->type_widths.find("VInt");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 33u);
}

TEST(TaggedUnionPackedRepr, UnpackedTaggedUnionWidthFromRealSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { void Invalid; bit [31:0] Valid; } VInt;\n"
      "  VInt u;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  auto it = design->type_widths.find("VInt");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 32u);
}

TEST(TaggedUnionPackedRepr, PackedTaggedUnionWidestMemberFromRealSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged packed { bit [7:0] N; bit [31:0] W; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  auto it = design->type_widths.find("U");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 33u);
}

TEST(TaggedUnionPackedRepr, RecursiveRepresentationForNestedTaggedUnion) {
  DataType inner;
  inner.kind = DataTypeKind::kUnion;
  inner.is_tagged = true;
  inner.is_packed = true;
  StructMember ix;
  ix.type_kind = DataTypeKind::kInt;
  ix.name = "X";
  StructMember iy;
  iy.type_kind = DataTypeKind::kInt;
  iy.name = "Y";
  inner.struct_members = {ix, iy};

  TypedefMap typedefs;
  typedefs["Inner"] = inner;

  DataType outer;
  outer.kind = DataTypeKind::kUnion;
  outer.is_tagged = true;
  outer.is_packed = true;
  StructMember big;
  big.type_kind = DataTypeKind::kNamed;
  big.type_name = "Inner";
  big.name = "Big";
  StructMember small;
  small.type_kind = DataTypeKind::kInt;
  small.name = "Small";
  outer.struct_members = {big, small};

  EXPECT_EQ(EvalTypeWidth(inner, typedefs), 33u);
  EXPECT_EQ(EvalTypeWidth(outer, typedefs), 34u);
}

TEST(TaggedUnionPackedRepr, PackedTaggedUnionLogicMembersFromRealSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged packed { logic [7:0] A; logic [15:0] B; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  auto it = design->type_widths.find("U");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 17u);
}

TEST(TaggedUnionValidation, PackedTaggedUnionEnumMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum bit [3:0] { R, G, B } col_t;\n"
      "  union tagged packed { col_t C; bit [7:0] V; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaggedUnionPackedRepr, PackedTaggedUnionNestedStructMemberFromRealSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged packed {\n"
      "    struct packed { bit [3:0] x; bit [3:0] y; } P;\n"
      "    bit [15:0] Q;\n"
      "  } U;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  auto it = design->type_widths.find("U");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 17u);
}

TEST(TaggedUnionValidation, PackedTaggedUnionShortrealMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { shortreal R; bit [31:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type of member 'R' is not allowed in a packed union", 2, "7.2.1"));
}

TEST(TaggedUnionValidation, PackedTaggedUnionUnpackedArrayMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { bit [7:0] arr [0:3]; bit [31:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked array member 'arr' is not allowed in a packed union", 2,
      "7.2.1"));
}

TEST(TaggedUnionValidation, PackedTaggedUnionStringMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { string S; bit [31:0] B; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type of member 'S' is not allowed in a packed union", 2, "7.2.1"));
}

TEST(TaggedUnionValidation, UnpackedUntaggedUnionVoidMember_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { void Invalid; int Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

void ExpectUnknownTagIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module top;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'U' has no member named 'Bogus'",
                            LineHolding(src, "tagged Bogus"), "11.9"));
}

TEST(TaggedUnionValidation, UnknownTagInAForkArm_Rejected) {
  ExpectUnknownTagIn(
      "fork\n"
      "      u = tagged Bogus 1;\n"
      "    join");
}

TEST(TaggedUnionValidation, UnknownTagInAForInit_Rejected) {
  ExpectUnknownTagIn("for (u = tagged Bogus 1; r == 0; r = 0) r = 1;");
}

TEST(TaggedUnionValidation, UnknownTagInAForStep_Rejected) {
  ExpectUnknownTagIn("for (r = 0; r == 0; u = tagged Bogus 1) r = 1;");
}

TEST(TaggedUnionValidation, UnknownTagInAnAssertionPassStmt_Rejected) {
  ExpectUnknownTagIn("assert (r) u = tagged Bogus 1;");
}

TEST(TaggedUnionValidation, UnknownTagInAnAssertionFailStmt_Rejected) {
  ExpectUnknownTagIn("assert (r) else u = tagged Bogus 1;");
}

TEST(TaggedUnionValidation, UnknownTagInARandcaseItem_Rejected) {
  ExpectUnknownTagIn("randcase 1: u = tagged Bogus 1; endcase");
}

TEST(TaggedUnionValidation, UnknownTagInARandsequenceCodeBlock_Rejected) {
  ExpectUnknownTagIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { u = tagged Bogus 1; };\n"
      "      endsequence\n"
      "    end");
}

constexpr std::string_view kNotPacked =
    "type of member 'a' is not allowed in a packed union";
constexpr std::string_view kUnpackedArray =
    "unpacked array member 'a' is not allowed in a packed union";
constexpr std::string_view kDynamicMember =
    "dynamic array, associative array or queue member 'd' can only be used in "
    "tagged unions";

TEST(TaggedUnionValidation,
     NonPackedMemberOfAPackedTaggedUnionReportedWhereverDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "typedef union tagged packed { real a; bit [7:0] b; } cu0_t;\n"
      "typedef union tagged packed { chandle a; bit [7:0] b; } cu1_t;\n"
      "typedef union tagged packed { bit [7:0] a; bit [15:0] b; void c; } "
      "cu2_t;\n"
      "package pk;\n"
      "  typedef union tagged packed { real a; bit [7:0] b; } pk0_t;\n"
      "  typedef union tagged packed { chandle a; bit [7:0] b; } pk1_t;\n"
      "  typedef union tagged packed { bit [7:0] a; bit [15:0] b; void c; } "
      "pk2_t;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  union tagged packed { real a; bit [7:0] b; } i0;\n"
      "  union tagged packed { chandle a; bit [7:0] b; } i1;\n"
      "  union tagged packed { bit [7:0] a; bit [15:0] b; void c; } i2;\n"
      "endinterface\n"
      "program pr;\n"
      "  union tagged packed { real a; bit [7:0] b; } p0;\n"
      "  union tagged packed { chandle a; bit [7:0] b; } p1;\n"
      "  union tagged packed { bit [7:0] a; bit [15:0] b; void c; } p2;\n"
      "endprogram\n"
      "checker ck;\n"
      "  union tagged packed { real a; bit [7:0] b; } c0;\n"
      "  union tagged packed { chandle a; bit [7:0] b; } c1;\n"
      "  union tagged packed { bit [7:0] a; bit [15:0] b; void c; } c2;\n"
      "endchecker\n"
      "class K;\n"
      "  union tagged packed { real a; bit [7:0] b; } k0;\n"
      "  union tagged packed { chandle a; bit [7:0] b; } k1;\n"
      "  union tagged packed { bit [7:0] a; bit [15:0] b; void c; } k2;\n"
      "endclass\n"
      "module top;\n"
      "  ifc ii(); pr p(); ck c();\n"
      "  if (1) begin : g\n"
      "    union tagged packed { real a; bit [7:0] b; } g0;\n"
      "    union tagged packed { chandle a; bit [7:0] b; } g1;\n"
      "    union tagged packed { bit [7:0] a; bit [15:0] b; void c; } g2;\n"
      "  end\n"
      "  function automatic void f;\n"
      "    union tagged packed { real a; bit [7:0] b; } f0;\n"
      "    union tagged packed { chandle a; bit [7:0] b; } f1;\n"
      "    union tagged packed { bit [7:0] a; bit [15:0] b; void c; } f2;\n"
      "  endfunction\n"
      "  task automatic t;\n"
      "    union tagged packed { real a; bit [7:0] b; } t0;\n"
      "    union tagged packed { chandle a; bit [7:0] b; } t1;\n"
      "    union tagged packed { bit [7:0] a; bit [15:0] b; void c; } t2;\n"
      "  endtask\n"
      "  initial begin\n"
      "    union tagged packed { real a; bit [7:0] b; } b0;\n"
      "    union tagged packed { chandle a; bit [7:0] b; } b1;\n"
      "    union tagged packed { bit [7:0] a; bit [15:0] b; void c; } b2;\n"
      "  end\n"
      "  cu0_t x0; cu1_t x1; cu2_t x2;\n"
      "  pk::pk0_t y0; pk::pk1_t y1; pk::pk2_t y2;\n"
      "  union tagged packed { real a; bit [7:0] b; } m0;\n"
      "  union tagged packed { chandle a; bit [7:0] b; } m1;\n"
      "  union tagged packed { bit [7:0] a; bit [15:0] b; void c; } m2;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {1,  2,  5,  6,  10, 11, 15, 16, 20, 21, 25,
                        26, 32, 33, 37, 38, 42, 43, 47, 48, 53, 54}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotPacked, line, "7.2.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 22u);
}

TEST(TaggedUnionValidation,
     DISABLED_TypedefOfADynamicMemberReportedWhereverDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int da_t [];\n"
      "typedef int q_t [$];\n"
      "typedef int aa_t [string];\n"
      "typedef union { da_t d; int i; } cu0_t;\n"
      "typedef union { q_t d; int i; } cu1_t;\n"
      "typedef union { aa_t d; int i; } cu2_t;\n"
      "typedef union tagged { da_t d; q_t q; aa_t m; int i; } cu3_t;\n"
      "package pk;\n"
      "  typedef union { da_t d; int i; } pk0_t;\n"
      "  typedef union { q_t d; int i; } pk1_t;\n"
      "  typedef union { aa_t d; int i; } pk2_t;\n"
      "  typedef union tagged { da_t d; q_t q; aa_t m; int i; } pk3_t;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  union { da_t d; int i; } i0;\n"
      "  union { q_t d; int i; } i1;\n"
      "  union { aa_t d; int i; } i2;\n"
      "  union tagged { da_t d; q_t q; aa_t m; int i; } i3;\n"
      "endinterface\n"
      "program pr;\n"
      "  union { da_t d; int i; } p0;\n"
      "  union { q_t d; int i; } p1;\n"
      "  union { aa_t d; int i; } p2;\n"
      "  union tagged { da_t d; q_t q; aa_t m; int i; } p3;\n"
      "endprogram\n"
      "checker ck;\n"
      "  union { da_t d; int i; } c0;\n"
      "  union { q_t d; int i; } c1;\n"
      "  union { aa_t d; int i; } c2;\n"
      "  union tagged { da_t d; q_t q; aa_t m; int i; } c3;\n"
      "endchecker\n"
      "class K;\n"
      "  union { da_t d; int i; } k0;\n"
      "  union { q_t d; int i; } k1;\n"
      "  union { aa_t d; int i; } k2;\n"
      "  union tagged { da_t d; q_t q; aa_t m; int i; } k3;\n"
      "endclass\n"
      "module top;\n"
      "  ifc ii(); pr p(); ck c();\n"
      "  if (1) begin : g\n"
      "    union { da_t d; int i; } g0;\n"
      "    union { q_t d; int i; } g1;\n"
      "    union { aa_t d; int i; } g2;\n"
      "    union tagged { da_t d; q_t q; aa_t m; int i; } g3;\n"
      "  end\n"
      "  function automatic void f;\n"
      "    union { da_t d; int i; } f0;\n"
      "    union { q_t d; int i; } f1;\n"
      "    union { aa_t d; int i; } f2;\n"
      "    union tagged { da_t d; q_t q; aa_t m; int i; } f3;\n"
      "  endfunction\n"
      "  task automatic t;\n"
      "    union { da_t d; int i; } t0;\n"
      "    union { q_t d; int i; } t1;\n"
      "    union { aa_t d; int i; } t2;\n"
      "    union tagged { da_t d; q_t q; aa_t m; int i; } t3;\n"
      "  endtask\n"
      "  initial begin\n"
      "    union { da_t d; int i; } b0;\n"
      "    union { q_t d; int i; } b1;\n"
      "    union { aa_t d; int i; } b2;\n"
      "    union tagged { da_t d; q_t q; aa_t m; int i; } b3;\n"
      "  end\n"
      "  cu0_t x0; cu1_t x1; cu2_t x2; cu3_t x3;\n"
      "  pk::pk0_t y0; pk::pk1_t y1; pk::pk2_t y2; pk::pk3_t y3;\n"
      "  union { da_t d; int i; } m0;\n"
      "  union { q_t d; int i; } m1;\n"
      "  union { aa_t d; int i; } m2;\n"
      "  union tagged { da_t d; q_t q; aa_t m; int i; } m3;\n"
      "endmodule\n",
      f);
  for (uint32_t line :
       {4,  5,  6,  9,  10, 11, 15, 16, 17, 21, 22, 23, 27, 28, 29, 33, 34,
        35, 41, 42, 43, 47, 48, 49, 53, 54, 55, 59, 60, 61, 66, 67, 68}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kDynamicMember, line, "7.3.2"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 33u);
}

TEST(TaggedUnionValidation,
     EveryNonPackedMemberKindOfAPackedTaggedUnionReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; endinterface\n"
      "typedef struct { bit [7:0] x; } us_t;\n"
      "module top;\n"
      "  union tagged packed { real a; bit [7:0] b; } h1;\n"
      "  union tagged packed { shortreal a; bit [7:0] b; } h2;\n"
      "  union tagged packed { chandle a; bit [7:0] b; } h3;\n"
      "  union tagged packed { event a; bit [7:0] b; } h4;\n"
      "  union tagged packed { string a; bit [7:0] b; } h5;\n"
      "  union tagged packed { us_t a; bit [7:0] b; } h6;\n"
      "  union tagged packed { virtual ifc a; bit [7:0] b; } h7;\n"
      "  union tagged packed { bit [7:0] a [2]; bit [7:0] b; } h8;\n"
      "  union tagged packed { bit [7:0] a []; bit [7:0] b; } h9;\n"
      "  union tagged packed { bit [7:0] a [$]; bit [7:0] b; } h10;\n"
      "  union tagged packed { bit [7:0] a [int]; bit [7:0] b; } h11;\n"
      "  union tagged packed { bit [7:0] a; struct packed { bit x; } b; void "
      "c; } ok;\n"
      "endmodule\n",
      f);
  for (uint32_t line = 4; line <= 10; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotPacked, line, "7.2.1"))
        << line;
  }
  for (uint32_t line = 11; line <= 14; ++line) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kUnpackedArray, line, "7.2.1"))
        << line;
  }
}

TEST(TaggedUnionValidation,
     DISABLED_ClassHandleMemberOfAPackedTaggedUnionReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "typedef C ct_t;\n"
      "module top;\n"
      "  union tagged packed { C a; bit [7:0] b; } h1;\n"
      "  union tagged packed { ct_t a; bit [7:0] b; } h2;\n"
      "  union tagged { C a; bit [7:0] b; } ok;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4, 5}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotPacked, line, "7.2.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
