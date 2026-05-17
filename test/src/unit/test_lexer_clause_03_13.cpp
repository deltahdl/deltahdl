#include "fixture_lexer.h"

using namespace delta;

namespace {

// §3.13(h): "The attribute name space is enclosed by the (* and *)
// constructs attached to a language element."  The lexer must recognize
// `(*` and `*)` as the attribute-instance delimiters distinct from the
// punctuation tokens used elsewhere.
TEST(NameSpaceLexing, AttributeNameSpaceDelimitersTokenized) {
  auto tokens = Lex("(* keep *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "keep");
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

// §3.13(b): "The package name space unifies all the package identifiers
// defined among all compilation units."  Lexing the `package` keyword
// surfaces the entry into that name space as a kKwPackage token, so the
// parser can register it.
TEST(NameSpaceLexing, PackageKeywordTokenized) {
  auto tokens = Lex("package my_pkg; endpackage");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPackage);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "my_pkg");
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndpackage);
}

// §3.13(a): "The definitions name space unifies all the non-nested
// module, primitive, program, and interface identifiers."  Each
// definition keyword must lex to its own distinct token kind so the
// parser/elaborator can populate the definitions name space.
TEST(NameSpaceLexing, DefinitionsNameSpaceKeywordsTokenized) {
  auto tokens = Lex("module primitive program interface");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwPrimitive);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwProgram);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwInterface);
}

}  // namespace
