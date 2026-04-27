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

static const GateKeywordEntry kGateKeywords[] = {
    {"and", TokenKind::kKwAnd},
    {"nand", TokenKind::kKwNand},
    {"or", TokenKind::kKwOr},
    {"nor", TokenKind::kKwNor},
    {"xor", TokenKind::kKwXor},
    {"xnor", TokenKind::kKwXnor},
    {"buf", TokenKind::kKwBuf},
    {"not", TokenKind::kKwNot},
    {"bufif0", TokenKind::kKwBufif0},
    {"bufif1", TokenKind::kKwBufif1},
    {"notif0", TokenKind::kKwNotif0},
    {"notif1", TokenKind::kKwNotif1},
    {"nmos", TokenKind::kKwNmos},
    {"pmos", TokenKind::kKwPmos},
    {"rnmos", TokenKind::kKwRnmos},
    {"rpmos", TokenKind::kKwRpmos},
    {"cmos", TokenKind::kKwCmos},
    {"rcmos", TokenKind::kKwRcmos},
    {"tran", TokenKind::kKwTran},
    {"rtran", TokenKind::kKwRtran},
    {"tranif0", TokenKind::kKwTranif0},
    {"tranif1", TokenKind::kKwTranif1},
    {"rtranif0", TokenKind::kKwRtranif0},
    {"rtranif1", TokenKind::kKwRtranif1},
    {"pullup", TokenKind::kKwPullup},
    {"pulldown", TokenKind::kKwPulldown},
};

TEST(GateKeywordLexing, KeywordSubstringIsIdentifier) {
  auto r = LexOne("ands");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(GateKeywordLexing, KeywordPrefixIsIdentifier) {
  auto r = LexOne("tranif");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

}  // namespace
