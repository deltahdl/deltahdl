// Non-LRM tests

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockLexing, EndprogramKeyword) {
  auto r = LexOne("endprogram");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprogram);
}

TEST(DesignBuildingBlockLexing, InterfaceKeyword) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(DesignBuildingBlockLexing, EndinterfaceKeyword) {
  auto r = LexOne("endinterface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndinterface);
}

TEST(DesignBuildingBlockLexing, CheckerKeyword) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(DesignBuildingBlockLexing, EndcheckerKeyword) {
  auto r = LexOne("endchecker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndchecker);
}

TEST(DesignBuildingBlockLexing, PackageKeyword) {
  auto r = LexOne("package");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPackage);
}

TEST(DesignBuildingBlockLexing, EndpackageKeyword) {
  auto r = LexOne("endpackage");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndpackage);
}

TEST(DesignBuildingBlockLexing, PrimitiveKeyword) {
  auto r = LexOne("primitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPrimitive);
}

TEST(DesignBuildingBlockLexing, EndprimitiveKeyword) {
  auto r = LexOne("endprimitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprimitive);
}

TEST(DesignBuildingBlockLexing, ConfigKeyword) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(DesignBuildingBlockLexing, EndconfigKeyword) {
  auto r = LexOne("endconfig");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(DesignBuildingBlockLexing, DesignElementKeywordsAreNotIdentifiers) {
  const char* keywords[] = {"module",    "program",   "interface",
                            "checker",   "package",   "primitive",
                            "config",    "macromodule"};
  for (const auto* kw : keywords) {
    auto r = LexOne(kw);
    EXPECT_NE(r.token.kind, TokenKind::kIdentifier)
        << kw << " should be a keyword, not an identifier";
  }
}

TEST(DesignBuildingBlockLexing, KeywordPrefixIsIdentifier) {
  auto r = LexOne("module_name");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(DesignBuildingBlockLexing, AllDesignElementKeywordsInSequence) {
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
