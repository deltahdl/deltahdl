#include "fixture_lexer.h"

using namespace delta;

namespace {

// §26.3 BNF (Syntax 26-2): package_import_item ::= package_identifier ::
// identifier.  The scope resolution operator `::` is the lexical hinge of
// every package reference; the lexer must produce a kColonColon token from
// the source text.
TEST(PackageReferenceLexing, ScopeResolutionOperatorTokenized) {
  auto tokens = Lex("pkg::ident");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "ident");
}

// §26.3 BNF (Syntax 26-2): package_import_item ::= package_identifier :: *.
// The wildcard form pairs `::` with a `*` punctuator token so the parser
// can distinguish explicit imports from wildcard imports.
TEST(PackageReferenceLexing, WildcardImportTokenSequence) {
  auto tokens = Lex("pkg::*");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

// §26.3: the `import` keyword introduces a package_import_declaration.  The
// lexer must classify it as the import keyword token rather than as an
// ordinary identifier.
TEST(PackageReferenceLexing, ImportKeywordTokenized) {
  auto tokens = Lex("import pkg::ident;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwImport);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

}  // namespace
