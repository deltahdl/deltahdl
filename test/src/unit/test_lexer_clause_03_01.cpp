#include "fixture_lexer.h"

using namespace delta;

namespace {

// §3.1 General — design element keyword tokenization.

TEST(DesignElementKeywordLexing, ModuleKeyword) {
  auto r = LexOne("module");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

TEST(DesignElementKeywordLexing, EndmoduleKeyword) {
  auto r = LexOne("endmodule");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndmodule);
}

TEST(DesignElementKeywordLexing, InterfaceKeyword) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(DesignElementKeywordLexing, EndinterfaceKeyword) {
  auto r = LexOne("endinterface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndinterface);
}

TEST(DesignElementKeywordLexing, ProgramKeyword) {
  auto r = LexOne("program");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProgram);
}

TEST(DesignElementKeywordLexing, EndprogramKeyword) {
  auto r = LexOne("endprogram");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprogram);
}

TEST(DesignElementKeywordLexing, CheckerKeyword) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(DesignElementKeywordLexing, EndcheckerKeyword) {
  auto r = LexOne("endchecker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndchecker);
}

TEST(DesignElementKeywordLexing, PackageKeyword) {
  auto r = LexOne("package");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPackage);
}

TEST(DesignElementKeywordLexing, EndpackageKeyword) {
  auto r = LexOne("endpackage");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndpackage);
}

TEST(DesignElementKeywordLexing, PrimitiveKeyword) {
  auto r = LexOne("primitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPrimitive);
}

TEST(DesignElementKeywordLexing, EndprimitiveKeyword) {
  auto r = LexOne("endprimitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprimitive);
}

TEST(DesignElementKeywordLexing, ConfigKeyword) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(DesignElementKeywordLexing, EndconfigKeyword) {
  auto r = LexOne("endconfig");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(DesignElementKeywordLexing, ModuleKeywordNotIdentifier) {
  auto r = LexOne("module");
  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
}

TEST(DesignElementKeywordLexing, ModulePrefixIsIdentifier) {
  auto r = LexOne("module_name");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(DesignElementKeywordLexing, AllDesignElementKeywordsInSequence) {
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
