#include <gtest/gtest.h>

#include <cstddef>
#include <string>

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

}  // namespace
