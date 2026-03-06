#include "fixture_lexer.h"

using namespace delta;

namespace {

// §3.1: Design elements are introduced by the keywords module, program,
// interface, checker, package, primitive, and config.

TEST(LexerClause03, Cl3_1_ModuleKeyword) {
  auto r = LexOne("module");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

TEST(LexerClause03, Cl3_1_EndmoduleKeyword) {
  auto r = LexOne("endmodule");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndmodule);
}

TEST(LexerClause03, Cl3_1_ProgramKeyword) {
  auto r = LexOne("program");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProgram);
}

TEST(LexerClause03, Cl3_1_EndprogramKeyword) {
  auto r = LexOne("endprogram");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprogram);
}

TEST(LexerClause03, Cl3_1_InterfaceKeyword) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(LexerClause03, Cl3_1_EndinterfaceKeyword) {
  auto r = LexOne("endinterface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndinterface);
}

TEST(LexerClause03, Cl3_1_CheckerKeyword) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(LexerClause03, Cl3_1_EndcheckerKeyword) {
  auto r = LexOne("endchecker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndchecker);
}

TEST(LexerClause03, Cl3_1_PackageKeyword) {
  auto r = LexOne("package");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPackage);
}

TEST(LexerClause03, Cl3_1_EndpackageKeyword) {
  auto r = LexOne("endpackage");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndpackage);
}

TEST(LexerClause03, Cl3_1_PrimitiveKeyword) {
  auto r = LexOne("primitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPrimitive);
}

TEST(LexerClause03, Cl3_1_EndprimitiveKeyword) {
  auto r = LexOne("endprimitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprimitive);
}

TEST(LexerClause03, Cl3_1_ConfigKeyword) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(LexerClause03, Cl3_1_EndconfigKeyword) {
  auto r = LexOne("endconfig");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(LexerClause03, Cl3_1_DesignElementKeywordsAreNotIdentifiers) {
  const char* keywords[] = {"module",    "program",   "interface",
                             "checker",  "package",   "primitive",
                             "config"};
  for (const auto* kw : keywords) {
    auto r = LexOne(kw);
    EXPECT_NE(r.token.kind, TokenKind::kIdentifier)
        << kw << " should be a keyword, not an identifier";
  }
}

}  // namespace
