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
      "MODULE",  "WIRE",    "REG",     "INPUT",   "OUTPUT",  "ALWAYS",
      "IF",      "ELSE",    "BEGIN",   "END",     "CLASS",   "LOGIC",
      "INT",     "FUNCTION", "TASK",   "PACKAGE", "IMPORT",  "TYPEDEF",
      "ENUM",    "STRUCT",   "INITIAL", "FINAL",  "DISABLE",
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

// §5.6.2 Statement 1: keywords whose lexeme contains underscores or trailing
// digits must still be recognized.  These exercise distinct entries in the
// keyword map and were not covered by the no-underscore samples above.
TEST(Keywords, UnderscoreContainingKeywordRecognized) {
  struct Sample {
    const char* text;
    TokenKind kind;
  };
  const Sample kSamples[] = {
      {"always_comb", TokenKind::kKwAlwaysComb},
      {"always_ff", TokenKind::kKwAlwaysFF},
      {"always_latch", TokenKind::kKwAlwaysLatch},
      {"join_any", TokenKind::kKwJoinAny},
      {"join_none", TokenKind::kKwJoinNone},
      {"s_always", TokenKind::kKwSAlways},
      {"s_until_with", TokenKind::kKwSUntilWith},
      {"unique0", TokenKind::kKwUnique0},
      {"wait_order", TokenKind::kKwWaitOrder},
  };
  for (const auto& s : kSamples) {
    auto r = LexOne(std::string(s.text) + " ");
    EXPECT_EQ(r.token.kind, s.kind) << s.text;
    EXPECT_EQ(r.token.text, s.text);
  }
}

// §5.6.2 Statement 3: case-sensitive map lookup must reject uppercase forms of
// underscore-containing keywords as well.
TEST(Keywords, UppercaseUnderscoreKeywordIsIdentifier) {
  const char* const kSamples[] = {
      "ALWAYS_COMB", "ALWAYS_FF",   "ALWAYS_LATCH", "JOIN_ANY",
      "JOIN_NONE",   "S_UNTIL_WITH", "WAIT_ORDER",   "UNIQUE0",
  };
  for (const char* upper : kSamples) {
    auto tokens = Lex(upper);
    ASSERT_GE(tokens.size(), 2u) << upper;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier) << upper;
  }
}

// §5.6.2 Statement 3: mixed case of underscore-containing keywords is also
// not recognized.
TEST(Keywords, MixedCaseUnderscoreKeywordIsIdentifier) {
  const char* const kSamples[] = {
      "Always_Comb", "Always_FF",   "Always_Latch", "Join_Any",
      "Join_None",   "S_Until_With", "Wait_Order",
  };
  for (const char* mixed : kSamples) {
    auto tokens = Lex(mixed);
    ASSERT_GE(tokens.size(), 2u) << mixed;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier) << mixed;
  }
}

// §5.6.2 Statement 2: the escape bypass applies to keywords whose lexeme
// contains underscores or trailing digits.
TEST(Keywords, EscapedUnderscoreKeywordIsIdentifier) {
  const char* const kSamples[] = {
      "always_comb",  "always_ff", "always_latch", "join_any",
      "join_none",    "s_always",  "s_until_with", "unique0",
      "wait_order",
  };
  for (const char* kw : kSamples) {
    std::string escaped = std::string("\\") + kw + " ";
    auto tokens = Lex(escaped);
    ASSERT_GE(tokens.size(), 2u) << kw;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier) << kw;
  }
}

// §5.6.2 Statement 1 boundary: a keyword followed immediately by punctuation
// (no intervening whitespace) must still be recognized.  The greedy identifier
// scan stops at the punctuation, and the keyword-map lookup is then applied to
// the keyword text alone.
TEST(Keywords, KeywordFollowedByPunctuation) {
  auto tokens = Lex("module;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[0].text, "module");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
}

TEST(Keywords, KeywordPrecededByPunctuation) {
  auto tokens = Lex("(module)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].text, "module");
  EXPECT_EQ(tokens[2].kind, TokenKind::kRParen);
}

// §5.6.2 Statement 2 boundary: an escaped keyword adjacent to punctuation is
// terminated by white space per §5.6.1, so without a trailing space the
// punctuation is consumed into the escaped-identifier body — verifying that
// the escape mechanism, not the keyword lookup, governs the token here.
TEST(Keywords, EscapedKeywordWithTrailingWhitespaceTerminates) {
  auto tokens = Lex("\\module ;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "module");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
}

}  // namespace
