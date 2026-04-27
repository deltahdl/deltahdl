// §3.2

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §3.2 names module, program, interface, checker, package, primitive, and
// config as the introducing keywords for the seven design-element kinds.
// Verify the lexer assigns the §3.2-specific token kind to each introducing
// keyword and to its matching end-keyword, so downstream parser dispatch can
// route each keyword to its corresponding design-element AST node. Each
// keyword landing on its own kKw* token kind also implies the lexeme is not
// classified as a generic identifier.
TEST(DesignElementKeywords, EachLexesToItsDistinctTokenKind) {
  auto tokens = Lex(
      "module endmodule interface endinterface "
      "program endprogram checker endchecker "
      "package endpackage primitive endprimitive "
      "config endconfig");
  ASSERT_GE(tokens.size(), 15u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwInterface);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndinterface);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwProgram);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwEndprogram);
  EXPECT_EQ(tokens[6].kind, TokenKind::kKwChecker);
  EXPECT_EQ(tokens[7].kind, TokenKind::kKwEndchecker);
  EXPECT_EQ(tokens[8].kind, TokenKind::kKwPackage);
  EXPECT_EQ(tokens[9].kind, TokenKind::kKwEndpackage);
  EXPECT_EQ(tokens[10].kind, TokenKind::kKwPrimitive);
  EXPECT_EQ(tokens[11].kind, TokenKind::kKwEndprimitive);
  EXPECT_EQ(tokens[12].kind, TokenKind::kKwConfig);
  EXPECT_EQ(tokens[13].kind, TokenKind::kKwEndconfig);
  EXPECT_EQ(tokens[14].kind, TokenKind::kEof);
}

}  // namespace
