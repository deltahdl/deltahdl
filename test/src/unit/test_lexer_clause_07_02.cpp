#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §7.2 does not introduce any new lexical productions of its own — the
// keywords it references (struct, union, packed, signed, unsigned, soft,
// tagged, void) are defined by §5.6.2 and tokenized by the keyword tables
// covered by the annex-a lexer tests. The struct_union and
// struct_union_member BNF rules cited in §7.2 are parsed in
// test_parser_clause_07_02.cpp.

// §7.2 anchor: confirm the `struct` and `union` keywords the subclause
// builds on tokenize as distinct keyword tokens — the parser tests in this
// clause depend on this separation.
TEST(StructUnionKeywords, StructAndUnionTokenizeDistinctly) {
  auto r1 = LexOne("struct");
  EXPECT_EQ(r1.token.kind, TokenKind::kKwStruct);
  auto r2 = LexOne("union");
  EXPECT_EQ(r2.token.kind, TokenKind::kKwUnion);
}

// §7.2 BNF anchor: the `struct_union ::= struct | union [ soft | tagged ]`
// rule names `soft` and `tagged` as union-only qualifiers. Confirm they
// reach the parser as distinct keyword tokens (the parser uses this to
// enforce the mutual-exclusion in test_parser_clause_07_02.cpp).
TEST(StructUnionKeywords, SoftAndTaggedTokenizeDistinctly) {
  auto rs = LexOne("soft");
  EXPECT_EQ(rs.token.kind, TokenKind::kKwSoft);
  auto rt = LexOne("tagged");
  EXPECT_EQ(rt.token.kind, TokenKind::kKwTagged);
}

// §7.2 BNF anchor: the `struct_union [ packed [ signing ] ]` production
// names `packed` as the optional structure-packing qualifier. Confirm
// the `packed` keyword tokenizes as its own kind so the parser can
// distinguish it from an identifier when applying footnote 17.
TEST(StructUnionKeywords, PackedTokenizesAsKeyword) {
  auto r = LexOne("packed");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPacked);
}

// §7.2 BNF anchor: the `data_type_or_void ::= data_type | void` production
// names `void` as the alternative struct_union_member member type used
// only inside tagged unions (footnote 20). Confirm `void` reaches the
// parser as its own keyword kind.
TEST(StructUnionKeywords, VoidTokenizesAsKeyword) {
  auto r = LexOne("void");
  EXPECT_EQ(r.token.kind, TokenKind::kKwVoid);
}

}  // namespace
