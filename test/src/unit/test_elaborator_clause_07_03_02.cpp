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

// The dynamic-types restriction covers string just as it covers chandle:
// outside a tagged union, a string member is not legal because there is no
// type-safe way to read it through a sibling member.
TEST(TaggedUnionValidation, StringInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { string S; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// Events are dynamic types too, so an event member is allowed only inside a
// tagged union — the tag is what makes a type-safe read of an event possible.
TEST(TaggedUnionValidation, EventInTaggedUnion_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged { event E; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// An event member of an untagged union must be rejected: without a tag the
// dynamic event handle could be reinterpreted through a sibling member.
TEST(TaggedUnionValidation, EventInUntaggedUnion_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union { event E; int I; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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

// Void members occupy no value bits: in a packed tagged union the only
// significant bits in a void-tagged value are the tag bits themselves.
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

// A void member next to a sized member contributes 0 to the member-width
// maximum; only the sized member determines the value-bit count.
TEST(TaggedUnionPackedRepr, VoidMemberContributesZeroBits) {
  DataType dt;
  dt.kind = DataTypeKind::kUnion;
  dt.is_tagged = true;
  dt.is_packed = true;
  StructMember v;
  v.type_kind = DataTypeKind::kVoid;
  v.name = "Invalid";
  StructMember i;
  i.type_kind = DataTypeKind::kInt;
  i.name = "Valid";
  dt.struct_members = {v, i};
  EXPECT_EQ(EvalTypeWidth(dt), 33u);
}

// Tag bits occupy the most-significant slot of the packed representation:
// for a two-member 32-bit-int union the tag is one bit at position 32.
TEST(TaggedUnionPackedRepr, TagBitsAreLeftJustified) {
  auto dt = MakePackedTaggedUnion(2);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 1u);
  EXPECT_EQ(TaggedUnionTagBitOffset(dt), 32u);
}

// Members occupy the low end of the representation, so the lowest tag bit
// sits immediately above the widest member's high bit. For five 32-bit
// members the tag is 3 bits wide starting at position 32.
TEST(TaggedUnionPackedRepr, MemberBitsAreRightJustified) {
  auto dt = MakePackedTaggedUnion(5);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 3u);
  EXPECT_EQ(TaggedUnionTagBitOffset(dt), 32u);
}

// A one-member tagged union needs no tag bits at all: zero bits suffice to
// distinguish a single name.
TEST(TaggedUnionPackedRepr, SingleMemberTaggedUnionHasZeroTagBits) {
  auto dt = MakePackedTaggedUnion(1);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 0u);
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
}

// At a power-of-two member count the tag width is exactly log2: four members
// fit in two tag bits, so the union is 34 bits wide.
TEST(TaggedUnionPackedRepr, FourMemberTagIsTwoBits) {
  auto dt = MakePackedTaggedUnion(4);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 2u);
  EXPECT_EQ(EvalTypeWidth(dt), 34u);
}

// Eight members also sit on a power-of-two boundary: three tag bits are
// sufficient, giving 35 bits total.
TEST(TaggedUnionPackedRepr, EightMemberTagIsThreeBits) {
  auto dt = MakePackedTaggedUnion(8);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 3u);
  EXPECT_EQ(EvalTypeWidth(dt), 35u);
}

// One past a power-of-two boundary forces the tag to grow: nine members need
// four tag bits.
TEST(TaggedUnionPackedRepr, NineMemberTagIsFourBits) {
  auto dt = MakePackedTaggedUnion(9);
  EXPECT_EQ(TaggedUnionTagWidth(dt), 4u);
  EXPECT_EQ(EvalTypeWidth(dt), 36u);
}

// A tagged-union expression can only name a member that the union actually
// declares; using an undeclared name in the tag position must elicit a
// diagnostic from the elaborator's tagged-expression check.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// The packed representation rule applies recursively: an outer packed tagged
// union whose member is itself a packed tagged union must account for the
// inner union's full representation, including its own tag bits.
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

}  // namespace
