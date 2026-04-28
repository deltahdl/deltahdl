// §5.6.2

#include <string>

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

TEST(Keywords, SimpleIdentKeywordDisambiguation) {
  auto tokens = Lex("module");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
}

TEST(Keywords, SimpleIdentNotKeyword) {
  auto tokens = Lex("modules");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "modules");
}

TEST(Keywords, ThisCaseSensitiveUppercase) {
  auto tokens = Lex("This");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(Keywords, ThisCaseSensitiveAllCaps) {
  auto tokens = Lex("THIS");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(Keywords, EscapedThisIsIdentifier) {
  auto tokens = Lex("\\this ");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

// §5.6.2: "All keywords are defined in lowercase only."
TEST(Keywords, UppercaseIsNotKeyword) {
  const char* const kSamples[] = {
      "MODULE", "WIRE",    "REG",    "INPUT",   "OUTPUT", "ALWAYS", "IF",
      "ELSE",   "BEGIN",   "END",    "CLASS",   "LOGIC",  "INT",    "FUNCTION",
      "TASK",   "PACKAGE", "IMPORT", "TYPEDEF", "ENUM",   "STRUCT",
  };
  for (const char* upper : kSamples) {
    auto tokens = Lex(upper);
    ASSERT_GE(tokens.size(), 2u) << "upper: " << upper;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << upper << " (uppercase) should be an identifier, not a keyword";
  }
}

TEST(Keywords, MixedCaseIsNotKeyword) {
  const char* const kSamples[] = {
      "Module",  "Wire",     "Reg",    "Input",      "Output",
      "Always",  "Begin",    "End",    "Class",      "Logic",
      "Int",     "Function", "Task",   "Package",    "Import",
      "Typedef", "Enum",     "Struct", "AlwaysComb", "AlwaysFF",
  };
  for (const char* mixed : kSamples) {
    auto tokens = Lex(mixed);
    ASSERT_GE(tokens.size(), 2u) << "mixed: " << mixed;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier)
        << mixed << " (mixed case) should be an identifier, not a keyword";
  }
}

// §5.6.2: "A SystemVerilog keyword preceded by an escape (backslash)
// character is not interpreted as a keyword."
TEST(Keywords, EscapedKeywordsAreIdentifiers) {
  const char* const kSamples[] = {
      "module",   "wire",     "reg",        "input",      "output",  "always",
      "if",       "else",     "begin",      "end",        "class",   "logic",
      "int",      "function", "task",       "package",    "import",  "typedef",
      "enum",     "struct",   "interface",  "program",    "checker", "clocking",
      "property", "sequence", "covergroup", "constraint", "assert",  "assume",
  };
  for (const char* kw : kSamples) {
    std::string escaped = std::string("\\") + kw + " ";
    auto tokens = Lex(escaped);
    ASSERT_GE(tokens.size(), 2u) << "escaped: " << kw;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier)
        << "\\" << kw << " should be an escaped identifier, not a keyword";
  }
}

TEST(GateKeywordLexing, KeywordSubstringIsIdentifier) {
  auto r = LexOne("ands");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

TEST(GateKeywordLexing, KeywordPrefixIsIdentifier) {
  auto r = LexOne("tranif");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
}

}  // namespace
