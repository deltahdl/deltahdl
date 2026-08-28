#include <string>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
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

// The tag size is the minimum number of bits needed to code all member
// names; five members fall in the five-to-eight range that needs 3 tag
// bits, so a five-member union of 32-bit members is 35 bits wide.
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

// The same chandle member is barred in an untagged union: only the tagged
// form makes such a member type-safe. §7.3.2 states "Dynamic types and chandle
// types shall not be used in untagged unions, but may be used in tagged
// unions", so the report names §7.3.2.
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

// The dynamic-types restriction covers string just as it covers chandle:
// outside a tagged union, a string member is not legal because there is no
// type-safe way to read it through a sibling member. The report names §7.3.2
// for the reason given above ChandleInUntaggedUnion_Rejected.
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
// dynamic event handle could be reinterpreted through a sibling member. The
// report names §7.3.2 for the reason given above
// ChandleInUntaggedUnion_Rejected.
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

// A real is not a packed type, so it cannot be a member of a packed union.
// §7.3.2 states no rule about member types; the rule is §7.2.1's "Only packed
// data types and the integer data types summarized in Table 6-8 shall be legal
// in packed structures", so the report names §7.2.1.
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
// diagnostic from the elaborator's tagged-expression check. §7.3.2 defers the
// rule with "Members of tagged unions can be referenced as tagged expressions.
// See 11.9", so the report names §11.9.
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

// A void member is legal in a packed tagged union: this is the packed VInt
// example, where the void arm carries no value bits and only the tag is
// significant. The packed-member-type check must not reject it.
TEST(TaggedUnionValidation, PackedTaggedUnionVoidMember_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union tagged packed { void Invalid; bit [31:0] Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The same void member is still barred in a packed untagged union, where no
// tag exists to make a value-less arm meaningful. The rule is syntax note 20)
// printed under Syntax 7-1 in §7.2, "It shall be legal to declare a void
// struct_union_member only within tagged unions", so the report names §7.2.
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

// The rule does not depend on where the union is declared. §3.12 makes a
// typedef at compilation-unit scope visible to every module, and its shape is
// checked there too -- so the same void member is rejected outside any module.
// The report names §7.2 for the reason given above
// PackedUntaggedUnionVoidMember_Rejected.
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

// End-to-end representation check: a packed tagged union declared from real
// source (the VInt shape, with a void arm) is elaborated to a type width of
// tag bits + widest member = 1 + 32 = 33. This drives the size rule through
// parse and elaboration rather than a hand-built type, and simultaneously
// exercises the void-arm case (a void member contributes zero value bits).
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

// The tag bits belong to the packed representation only: the same tagged union
// declared without the packed qualifier is elaborated to just the widest
// member's width, with no in-vector tag. Observed end-to-end from real source.
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

// Members of a packed tagged union need not be the same size: the value-bit
// count follows the widest member. From real source, an 8-bit and a 32-bit arm
// give a 33-bit representation (1 tag bit + max(8, 32)).
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

// A packed tagged union accepts 4-state packed members (logic), not just
// 2-state ones. Driven from real source: two logic arms of differing widths
// elaborate cleanly and the representation is tag + widest member = 1 + 16.
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

// An enumeration type is a packed type, so it is an admissible member of a
// packed tagged union. The type is produced by a real enum declaration and the
// union member references it by name.
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

// A packed structure is itself a packed type and may be a member of a packed
// tagged union. The representation rule applies through the nested aggregate:
// the widest member is the 16-bit arm, giving tag + 16 = 17 bits. Built from
// real nested-struct source rather than a hand-assembled type.
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

// A shortreal is not a packed type, so it cannot be a member of a packed
// tagged union — the packed-member-type rule rejects it, just as it rejects a
// real member. The report names §7.2.1 for the reason given above
// PackedTaggedUnionRealMember_Rejected.
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

// An unpacked array is not a packed type. Even though its element type is
// packed, the unpacked dimension makes the member itself unpacked, so it is
// rejected as a member of a packed tagged union. §7.3.2 states no rule about
// member types; the rule is §7.2.1's restriction to packed data types, so the
// report names §7.2.1.
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

// A string member is legal in an unpacked tagged union (a string is a dynamic
// type made type-safe by the tag), but a string is not a packed type, so the
// same member is rejected once the union carries the packed qualifier. The
// report names §7.2.1 for the reason given above
// PackedTaggedUnionRealMember_Rejected.
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

// The negative form of the void-member rule at the other syntactic position:
// an unpacked untagged union may not carry a void member, since without a tag
// there is no way to know when the void arm is the active one. The report
// names §7.2 for the reason given above PackedUntaggedUnionVoidMember_Rejected.
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

// §7.3.2 defers the rule on a tagged expression to §11.9 -- "Members of tagged
// unions can be referenced as tagged expressions. See 11.9" -- and §11.9
// requires the name written after `tagged` to be a member of the target's
// tagged union type. CheckTaggedMemberName in
// src/elaborator/elaborator_validate_operations.cpp is that rule, and
// WalkStmtsForTaggedExpr carries it down a statement tree, judging every
// blocking and nonblocking assignment it reaches.
//
// That walk wrote out six of the thirteen child-statement links Stmt declares
// and now takes the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The seven cases below cover
// one newly reached position each, and each elaborated clean before the
// conversion, accepting a tag name the union does not declare.
//
// `stmt` is written at line 6 of the source and may run to several lines, so
// the line the report stands at is read back out of the source rather than
// counted.
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

// §9.3.2 gives `fork { statement_or_null } join`, whose arms the parser keeps
// in Stmt::fork_stmts.
TEST(TaggedUnionValidation, UnknownTagInAForkArm_Rejected) {
  ExpectUnknownTagIn(
      "fork\n"
      "      u = tagged Bogus 1;\n"
      "    join");
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, and A.8.3 makes a
// tagged_union_expression an alternative of expression, so the assignment
// stands in a for-loop initialization. The parser keeps it in Stmt::for_inits.
TEST(TaggedUnionValidation, UnknownTagInAForInit_Rejected) {
  ExpectUnknownTagIn("for (u = tagged Bogus 1; r == 0; r = 0) r = 1;");
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// is a variable_lvalue, an assignment_operator and an expression, so the same
// assignment stands in a for-loop step. The parser keeps it in Stmt::for_steps.
TEST(TaggedUnionValidation, UnknownTagInAForStep_Rejected) {
  ExpectUnknownTagIn("for (r = 0; r == 0; u = tagged Bogus 1) r = 1;");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the next cover one arm each.
TEST(TaggedUnionValidation, UnknownTagInAnAssertionPassStmt_Rejected) {
  ExpectUnknownTagIn("assert (r) u = tagged Bogus 1;");
}

TEST(TaggedUnionValidation, UnknownTagInAnAssertionFailStmt_Rejected) {
  ExpectUnknownTagIn("assert (r) else u = tagged Bogus 1;");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §11.9 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(TaggedUnionValidation, UnknownTagInARandcaseItem_Rejected) {
  ExpectUnknownTagIn("randcase 1: u = tagged Bogus 1; endcase");
}

// §18.17 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(TaggedUnionValidation, UnknownTagInARandsequenceCodeBlock_Rejected) {
  ExpectUnknownTagIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { u = tagged Bogus 1; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
