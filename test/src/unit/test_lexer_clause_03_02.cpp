#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause03, ModuleKeyword) {
  auto r = LexOne("module");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

TEST(LexerClause03, EndmoduleKeyword) {
  auto r = LexOne("endmodule");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndmodule);
}

TEST(LexerClause03, MacromoduleKeyword) {
  auto r = LexOne("macromodule");
  EXPECT_EQ(r.token.kind, TokenKind::kKwMacromodule);
}

TEST(LexerClause03, ProgramKeyword) {
  auto r = LexOne("program");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProgram);
}

TEST(LexerClause03, EndprogramKeyword) {
  auto r = LexOne("endprogram");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprogram);
}

TEST(LexerClause03, InterfaceKeyword) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(LexerClause03, EndinterfaceKeyword) {
  auto r = LexOne("endinterface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndinterface);
}

TEST(LexerClause03, CheckerKeyword) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(LexerClause03, EndcheckerKeyword) {
  auto r = LexOne("endchecker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndchecker);
}

TEST(LexerClause03, PackageKeyword) {
  auto r = LexOne("package");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPackage);
}

TEST(LexerClause03, EndpackageKeyword) {
  auto r = LexOne("endpackage");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndpackage);
}

TEST(LexerClause03, PrimitiveKeyword) {
  auto r = LexOne("primitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPrimitive);
}

TEST(LexerClause03, EndprimitiveKeyword) {
  auto r = LexOne("endprimitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprimitive);
}

TEST(LexerClause03, ConfigKeyword) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(LexerClause03, EndconfigKeyword) {
  auto r = LexOne("endconfig");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(LexerClause03, DesignElementKeywordsAreNotIdentifiers) {
  const char* keywords[] = {"module",    "program",   "interface",
                            "checker",   "package",   "primitive",
                            "config",    "macromodule"};
  for (const auto* kw : keywords) {
    auto r = LexOne(kw);
    EXPECT_NE(r.token.kind, TokenKind::kIdentifier)
        << kw << " should be a keyword, not an identifier";
  }
}

}  // namespace
