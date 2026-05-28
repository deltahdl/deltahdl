#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Build a packed tagged union data type with `count` integer members.
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

// The packed representation size is the tag width plus the maximum member
// size: two 32-bit members need a 1-bit tag, giving 33 bits.
TEST(TaggedUnionPackedRepr, SizeIsTagPlusMaxMember) {
  EXPECT_EQ(EvalTypeWidth(MakePackedTaggedUnion(2)), 33u);
}

// The tag size is the minimum number of bits needed to code all member
// names; five members fall in the five-to-eight range that needs 3 tag
// bits, so a five-member union of 32-bit members is 35 bits wide.
TEST(TaggedUnionPackedRepr, TagWidthCoversAllMemberNames) {
  EXPECT_EQ(EvalTypeWidth(MakePackedTaggedUnion(5)), 35u);
}

// The tag bits are part of the packed representation only; an unpacked
// tagged union carries no in-vector tag, so its width is just the widest
// member.
TEST(TaggedUnionPackedRepr, UnpackedTaggedUnionHasNoTagBits) {
  DataType dt = MakePackedTaggedUnion(2);
  dt.is_packed = false;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
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

// The same chandle member is barred in an untagged union: only the tagged
// form makes such a member type-safe.
TEST(TaggedUnionValidation, ChandleInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { chandle Handle; int Value; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(TaggedUnionValidation, MultipleVoidMembers_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { void A; void B; int C; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}
