// §5.6.2

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(Keywords, ModuleKeyword) {
  auto r = LexOne("module");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

TEST(Keywords, EndmoduleKeyword) {
  auto r = LexOne("endmodule");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndmodule);
}

TEST(Keywords, MacromoduleKeyword) {
  auto r = LexOne("macromodule");
  EXPECT_EQ(r.token.kind, TokenKind::kKwMacromodule);
}

TEST(Keywords, ProgramKeyword) {
  auto r = LexOne("program");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProgram);
}

TEST(Keywords, EndprogramKeyword) {
  auto r = LexOne("endprogram");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprogram);
}

TEST(Keywords, InterfaceKeyword) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(Keywords, EndinterfaceKeyword) {
  auto r = LexOne("endinterface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndinterface);
}

TEST(Keywords, CheckerKeyword) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(Keywords, EndcheckerKeyword) {
  auto r = LexOne("endchecker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndchecker);
}

TEST(Keywords, PackageKeyword) {
  auto r = LexOne("package");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPackage);
}

TEST(Keywords, EndpackageKeyword) {
  auto r = LexOne("endpackage");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndpackage);
}

TEST(Keywords, PrimitiveKeyword) {
  auto r = LexOne("primitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPrimitive);
}

TEST(Keywords, EndprimitiveKeyword) {
  auto r = LexOne("endprimitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprimitive);
}

TEST(Keywords, ConfigKeyword) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(Keywords, EndconfigKeyword) {
  auto r = LexOne("endconfig");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndconfig);
}

TEST(Keywords, DesignElementKeywordsAreNotIdentifiers) {
  const char* keywords[] = {"module",    "program",   "interface",
                            "checker",   "package",   "primitive",
                            "config",    "macromodule"};
  for (const auto* kw : keywords) {
    auto r = LexOne(kw);
    EXPECT_NE(r.token.kind, TokenKind::kIdentifier)
        << kw << " should be a keyword, not an identifier";
  }
}

TEST(Keywords, UppercaseNotKeyword) {
  auto r = LexOne("Module ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "Module");
}

TEST(Keywords, AllUppercaseNotKeyword) {
  auto r = LexOne("MODULE ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "MODULE");
}

TEST(Keywords, MixedCaseVariantsNotKeywords) {
  const char* const mixed[] = {"Module", "BEGIN", "Logic", "WIRE", "AlwayS"};
  for (const char* m : mixed) {
    std::string input = std::string(m) + " ";
    auto r = LexOne(input);
    EXPECT_EQ(r.token.kind, TokenKind::kIdentifier)
        << m << " should be an identifier, not a keyword";
  }
}

TEST(Keywords, DataTypeKeywordRecognized) {
  auto r = LexOne("logic");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLogic);
}

TEST(Keywords, ControlFlowKeywordRecognized) {
  auto r = LexOne("if");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIf);
}

TEST(Keywords, KeywordPrefixIsIdentifier) {
  auto r = LexOne("module_name");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(Keywords, KeywordSuffixIsIdentifier) {
  auto r = LexOne("endmodule_x");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(Keywords, AllDesignElementKeywordsInSequence) {
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
