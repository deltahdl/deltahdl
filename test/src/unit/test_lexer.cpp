#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

TEST(Lexer, EmptyInput) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].IsEof());
}

// --- §5.2: Lexical tokens ---

TEST(Lexer, LexicalToken_SourceIsTokenStream) {
  // §5.2: "SystemVerilog source text files shall be a stream of lexical
  // tokens."
  auto tokens = Lex("module m; endmodule");
  ASSERT_GE(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndmodule);
  EXPECT_TRUE(tokens.back().IsEof());
}

TEST(Lexer, LexicalToken_EachTokenHasOneOrMoreChars) {
  // §5.2: "A lexical token shall consist of one or more characters."
  auto tokens = Lex("module m; logic [7:0] x = 8'hFF + 1; endmodule");
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    EXPECT_GE(tokens[i].text.size(), 1u)
        << "token " << i << " (" << tokens[i].text << ") is empty";
  }
}

TEST(Lexer, LexicalToken_FreeFormatLayout) {
  // §5.2: "The layout of tokens in a source file shall be free format; that
  // is, spaces and newline characters shall not be syntactically significant
  // other than being token separators."
  auto compact = Lex("module m;logic [7:0] x;endmodule");
  auto spread =
      Lex("module\n  m\n  ;\nlogic\n  [\n  7\n  :\n  0\n  ]\n  x\n  "
          ";\nendmodule\n");
  std::vector<TokenKind> ck, sk;
  for (auto& t : compact)
    if (!t.IsEof()) ck.push_back(t.kind);
  for (auto& t : spread)
    if (!t.IsEof()) sk.push_back(t.kind);
  EXPECT_EQ(ck, sk);
}

TEST(Lexer, LexicalToken_FreeFormatTokenText) {
  // §5.2: Free format — token text is identical regardless of layout.
  auto compact = Lex("module m;logic [7:0] x;endmodule");
  auto spread =
      Lex("module\n  m\n  ;\nlogic\n  [\n  7\n  :\n  0\n  ]\n  x\n  "
          ";\nendmodule\n");
  std::vector<std::string> ct, st;
  for (auto& t : compact)
    if (!t.IsEof()) ct.emplace_back(t.text);
  for (auto& t : spread)
    if (!t.IsEof()) st.emplace_back(t.text);
  EXPECT_EQ(ct, st);
}

TEST(Lexer, LexicalToken_AllSevenCategories) {
  // §5.2: Token types — White space, Comment, Operator, Number, String
  // literal, Identifier, Keyword. White space and comments are consumed by the
  // lexer (not emitted as tokens). Verify the remaining 5 emitted categories.
  auto tokens = Lex("module /* comment */ x ; x = 42 + \"hello\" ; endmodule");
  bool has_keyword = false, has_id = false, has_op = false;
  bool has_number = false, has_string = false;
  for (auto& t : tokens) {
    if (t.kind == TokenKind::kKwModule || t.kind == TokenKind::kKwEndmodule)
      has_keyword = true;
    if (t.kind == TokenKind::kIdentifier) has_id = true;
    if (t.kind == TokenKind::kPlus || t.kind == TokenKind::kEq) has_op = true;
    if (t.kind == TokenKind::kIntLiteral) has_number = true;
    if (t.kind == TokenKind::kStringLiteral) has_string = true;
  }
  EXPECT_TRUE(has_keyword);
  EXPECT_TRUE(has_id);
  EXPECT_TRUE(has_op);
  EXPECT_TRUE(has_number);
  EXPECT_TRUE(has_string);
}

TEST(Lexer, LexicalToken_EscapedIdentifierException) {
  // §5.2: "except for escaped identifiers (see 5.6.1)" — whitespace IS
  // syntactically significant for escaped identifiers: it terminates them.
  auto with_space = Lex("\\abc+def ");
  ASSERT_GE(with_space.size(), 2);
  EXPECT_EQ(with_space[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(with_space[0].text, "\\abc+def");

  auto with_tab = Lex("\\abc+def\t");
  EXPECT_EQ(with_tab[0].text, "\\abc+def");

  auto with_newline = Lex("\\abc+def\n");
  EXPECT_EQ(with_newline[0].text, "\\abc+def");
}

TEST(Lexer, LexicalToken_CommentsActAsSeparators) {
  // §5.2: Comments are one of the 7 token types. Like whitespace, they
  // separate adjacent tokens.
  auto tokens = Lex("module/**/m;endmodule");
  ASSERT_GE(tokens.size(), 5);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "m");
}

// --- §5.3: White space ---

TEST(Lexer, Whitespace_SpaceSeparatesTokens) {
  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_TabSeparatesTokens) {
  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_NewlineSeparatesTokens) {
  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_FormfeedSeparatesTokens) {
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_CarriageReturnSeparatesTokens) {
  auto tokens = Lex("a\rb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_CrLfSeparatesTokens) {
  auto tokens = Lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_MixedWhitespace) {
  auto tokens = Lex("a \t\n \f b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_LeadingAndTrailing) {
  auto tokens = Lex("  \t a \n  ");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_TRUE(tokens[1].IsEof());
}

TEST(Lexer, Whitespace_OnlyWhitespace) {
  auto tokens = Lex("   \t\n\f  ");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].IsEof());
}

TEST(Lexer, Whitespace_VerticalTab) {
  // \v (vertical tab) is whitespace per std::isspace.
  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_NotInTokenText) {
  // §5.3: whitespace is ignored — it must not appear in token text.
  auto tokens = Lex("  module  \t endmodule \n ");
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "module");
  EXPECT_EQ(tokens[1].text, "endmodule");
}

TEST(Lexer, Whitespace_SeparatesAdjacentIdentifiers) {
  // §5.3: whitespace serves to separate tokens — without it,
  // "ab" is one identifier; with space, "a b" is two.
  auto one = Lex("ab");
  ASSERT_EQ(one.size(), 2);
  EXPECT_EQ(one[0].text, "ab");

  auto two = Lex("a b");
  ASSERT_EQ(two.size(), 3);
  EXPECT_EQ(two[0].text, "a");
  EXPECT_EQ(two[1].text, "b");
}

TEST(Lexer, Whitespace_NotRequiredBetweenPunctuationAndIdentifier) {
  // §5.3: whitespace only *serves* to separate when needed;
  // punctuation self-delimits, so no whitespace is required.
  auto tokens = Lex("a;b");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(Lexer, Whitespace_EofTerminatesTokenStream) {
  // §5.3: end of file is a whitespace character — it terminates the stream.
  auto tokens = Lex("x");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].text, "x");
  EXPECT_TRUE(tokens[1].IsEof());
}

TEST(Lexer, Whitespace_StringLiteralPreservesSpacesAndTabs) {
  // §5.3: blanks and tabs are significant in string literals.
  auto tokens = Lex("\"a \t b\"");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_NE(tokens[0].text.find(" \t "), std::string_view::npos);
}

TEST(Lexer, Whitespace_StringLiteralPreservesMultipleSpaces) {
  // §5.3: blanks are significant — multiple spaces are not collapsed.
  auto tokens = Lex("\"   \"");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_NE(tokens[0].text.find("   "), std::string_view::npos);
}

TEST(Lexer, Whitespace_FormfeedOnly) {
  // §5.3: formfeed is whitespace; a source with only formfeed yields EOF.
  auto tokens = Lex("\f");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].IsEof());
}

TEST(Lexer, Whitespace_ConsecutiveFormfeeds) {
  // §5.3: multiple formfeeds act as whitespace, separating tokens.
  auto tokens = Lex("a\f\f\fb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// --- §5.6.2: Keywords ---

TEST(Lexer, Keyword_Basic) {
  auto tokens = Lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
  EXPECT_TRUE(tokens[2].IsEof());
}

TEST(Lexer, Keyword_LowercaseOnly) {
  // §5.6.2: keywords are lowercase only. Uppercase = identifier.
  auto tokens = Lex("Module MODULE");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(Lexer, Keyword_EscapedKeywordIsIdentifier) {
  // §5.6.2: keyword preceded by backslash is not a keyword
  auto tokens = Lex("\\module ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

// --- §5.6: Identifiers, keywords, and system names ---

TEST(Lexer, Identifier_SimpleLettersDigitsUnderscore) {
  auto tokens = Lex("foo bar_123 _baz");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar_123");
  EXPECT_EQ(tokens[2].text, "_baz");
}

TEST(Lexer, Identifier_WithDollarSign) {
  // §5.6: $ is allowed in simple identifiers (but not first char)
  auto tokens = Lex("n$657");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "n$657");
}

TEST(Lexer, Identifier_CaseSensitive) {
  // §5.6: identifiers are case sensitive
  auto tokens = Lex("Foo foo FOO");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "Foo");
  EXPECT_EQ(tokens[1].text, "foo");
  EXPECT_EQ(tokens[2].text, "FOO");
  // All three are distinct identifiers
  EXPECT_NE(tokens[0].text, tokens[1].text);
}

TEST(Lexer, Identifier_UnderscoreStart) {
  // §5.6: first char can be underscore
  auto tokens = Lex("_bus3");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_bus3");
}

TEST(Lexer, Identifier_LrmExamples) {
  // §5.6 examples: shiftreg_a, busa_index, error_condition, merge_ab
  for (const char* id :
       {"shiftreg_a", "busa_index", "error_condition", "merge_ab"}) {
    auto tokens = Lex(id);
    ASSERT_GE(tokens.size(), 2) << id;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier) << id;
    EXPECT_EQ(tokens[0].text, id) << id;
  }
}

// --- §5.6.1: Escaped identifiers ---

TEST(Lexer, EscapedIdent_StartBackslashEndWhitespace) {
  // §5.6.1: Start with \, end with white space; whitespace not in token.
  auto sp = Lex("\\foo ");
  ASSERT_GE(sp.size(), 2);
  EXPECT_EQ(sp[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(sp[0].text, "\\foo");
  EXPECT_EQ(Lex("\\bar\t")[0].text, "\\bar");
  EXPECT_EQ(Lex("\\baz\n")[0].text, "\\baz");
  // §5.6.1: Printable ASCII 33-126 allowed.
  EXPECT_EQ(Lex("\\!@#$%^&*() ")[0].text, "\\!@#$%^&*()");
}

TEST(Lexer, EscapedIdent_LrmExamples) {
  // §5.6.1 examples from the LRM.
  const char* cases[][2] = {
      {"\\busa+index ", "\\busa+index"},
      {"\\-clock ", "\\-clock"},
      {"\\***error-condition*** ", "\\***error-condition***"},
      {"\\{a,b} ", "\\{a,b}"},
      {"\\a*(b+c) ", "\\a*(b+c)"}};
  for (auto& c : cases) {
    EXPECT_EQ(Lex(c[0])[0].kind, TokenKind::kEscapedIdentifier) << c[0];
    EXPECT_EQ(Lex(c[0])[0].text, c[1]) << c[0];
  }
}

TEST(Lexer, EscapedIdent_MultipleEscapedKeywords) {
  // §5.6.1: An escaped keyword is treated as a user-defined identifier.
  for (const char* kw : {"\\module ", "\\begin ", "\\wire ", "\\always "}) {
    auto tokens = Lex(kw);
    ASSERT_GE(tokens.size(), 2) << kw;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier) << kw;
  }
}

// --- §5.7: Numbers (dispatch: integral vs real vs time) ---

TEST(Lexer, Number_IntegerLiterals) {
  auto tokens = Lex("42 8'hFF 4'b1010");
  struct Case {
    TokenKind kind;
    std::string text;
  };
  Case expected[] = {
      {TokenKind::kIntLiteral, "42"},
      {TokenKind::kIntLiteral, "8'hFF"},
      {TokenKind::kIntLiteral, "4'b1010"},
  };
  ASSERT_EQ(tokens.size(), std::size(expected) + 1);
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(tokens[i].kind, expected[i].kind) << "token " << i;
    EXPECT_EQ(tokens[i].text, expected[i].text) << "token " << i;
  }
}

TEST(Lexer, Number_DispatchIntRealTime) {
  // §5.7: number is integral_number or real_number; time_literal adds unit
  auto tokens = Lex("42 3.14 100ns");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kTimeLiteral);
}

// --- §5.9: String literals ---

TEST(Lexer, String_Basic) {
  auto tokens = Lex("\"Hello, World!\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"Hello, World!\"");
}

TEST(Lexer, String_Empty) {
  auto tokens = Lex("\"\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

TEST(Lexer, String_WithEscapedQuote) {
  auto tokens = Lex("\"say \\\"hi\\\"\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, String_WithEscapedBackslash) {
  auto tokens = Lex("\"path\\\\dir\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, String_TripleQuotedWithUnescapedQuotes) {
  // §5.9: triple-quoted strings allow " without escape
  auto tokens = Lex(R"("""a "quoted" word""")");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, String_TripleQuotedWithNewline) {
  // §5.9: triple-quoted strings allow direct newlines
  auto tokens = Lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// --- §5.6.3: System tasks and system functions ---

TEST(Lexer, SystemTf_Basic) {
  auto tokens = Lex("$display $finish");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].text, "$finish");
}

TEST(Lexer, SystemTf_EmbeddedDollar) {
  // §5.6.3: system_tf_identifier allows $ within the name
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(Lexer, SystemTf_WithDigitsAndUnderscore) {
  auto tokens = Lex("$urandom_range $stime");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$urandom_range");
  EXPECT_EQ(tokens[1].text, "$stime");
}

TEST(Lexer, SystemTf_LrmExamples) {
  // §5.6.3 examples
  auto tokens = Lex("$display $finish");
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
}

TEST(Lexer, SystemTf_DollarAloneIsNotSystem) {
  // Bare $ followed by non-alpha is just kDollar, not a system identifier
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

// --- §5.6.4: Compiler directives ---
// NOTE: Directives (`) are handled by the preprocessor before lexing.
// Preprocessor coverage is in test_lexical.cpp (§22.5, §22.6, §22.14).
// The lexer sees backtick as an unexpected character if it reaches it.

TEST(Lexer, CompilerDirective_BacktickIsUnexpected) {
  // If a backtick reaches the lexer (not preprocessed), it's an error.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "`define FOO 1");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

// --- §5.5: Operators ---

TEST(Lexer, Operators_SingleChar) {
  auto tokens = Lex("+ - * / % & | ^ ~ ! = < > ?");
  TokenKind expected[] = {
      TokenKind::kPlus,  TokenKind::kMinus,    TokenKind::kStar,
      TokenKind::kSlash, TokenKind::kPercent,  TokenKind::kAmp,
      TokenKind::kPipe,  TokenKind::kCaret,    TokenKind::kTilde,
      TokenKind::kBang,  TokenKind::kEq,       TokenKind::kLt,
      TokenKind::kGt,    TokenKind::kQuestion,
  };
  ASSERT_EQ(tokens.size(), std::size(expected) + 1);
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(tokens[i].kind, expected[i]) << "token " << i;
  }
}

TEST(Lexer, Operators_DoubleChar) {
  auto tokens =
      Lex("== != <= >= << >> && || ** ++ -- -> => :: ~& ~| ~^ ^~ .* ## @@");
  TokenKind expected[] = {
      TokenKind::kEqEq,      TokenKind::kBangEq,     TokenKind::kLtEq,
      TokenKind::kGtEq,      TokenKind::kLtLt,       TokenKind::kGtGt,
      TokenKind::kAmpAmp,    TokenKind::kPipePipe,   TokenKind::kPower,
      TokenKind::kPlusPlus,  TokenKind::kMinusMinus, TokenKind::kArrow,
      TokenKind::kEqGt,      TokenKind::kColonColon, TokenKind::kTildeAmp,
      TokenKind::kTildePipe, TokenKind::kTildeCaret, TokenKind::kCaretTilde,
      TokenKind::kDotStar,   TokenKind::kHashHash,   TokenKind::kAtAt,
  };
  ASSERT_EQ(tokens.size(), std::size(expected) + 1);
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(tokens[i].kind, expected[i]) << "token " << i;
  }
}

TEST(Lexer, Operators_TripleChar) {
  auto tokens = Lex("=== !== ==? !=? <<< >>> ->> |-> |=> <-> &&&");
  TokenKind expected[] = {
      TokenKind::kEqEqEq,       TokenKind::kBangEqEq,
      TokenKind::kEqEqQuestion, TokenKind::kBangEqQuestion,
      TokenKind::kLtLtLt,       TokenKind::kGtGtGt,
      TokenKind::kDashGtGt,     TokenKind::kPipeDashGt,
      TokenKind::kPipeEqGt,     TokenKind::kLtDashGt,
      TokenKind::kAmpAmpAmp,
  };
  ASSERT_EQ(tokens.size(), std::size(expected) + 1);
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(tokens[i].kind, expected[i]) << "token " << i;
  }
}

TEST(Lexer, Operators_CompoundAssignment) {
  auto tokens = Lex("+= -= *= /= %= &= |= ^= <<= >>= <<<= >>>=");
  TokenKind expected[] = {
      TokenKind::kPlusEq,  TokenKind::kMinusEq,   TokenKind::kStarEq,
      TokenKind::kSlashEq, TokenKind::kPercentEq, TokenKind::kAmpEq,
      TokenKind::kPipeEq,  TokenKind::kCaretEq,   TokenKind::kLtLtEq,
      TokenKind::kGtGtEq,  TokenKind::kLtLtLtEq,  TokenKind::kGtGtGtEq,
  };
  ASSERT_EQ(tokens.size(), std::size(expected) + 1);
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(tokens[i].kind, expected[i]) << "token " << i;
  }
}

TEST(Lexer, Operators_IndexedPartSelect) {
  auto tokens = Lex("+: -:");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusColon);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusColon);
}

TEST(Lexer, Operators_Tolerance) {
  auto tokens = Lex("+/- +%-");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusSlashMinus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPercentMinus);
}

TEST(Lexer, Operators_StarGt) {
  auto tokens = Lex("*>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStarGt);
}

TEST(Lexer, Punctuation) {
  auto tokens = Lex("( ) [ ] { } ; , . : # @");
  TokenKind expected[] = {
      TokenKind::kLParen,    TokenKind::kRParen, TokenKind::kLBracket,
      TokenKind::kRBracket,  TokenKind::kLBrace, TokenKind::kRBrace,
      TokenKind::kSemicolon, TokenKind::kComma,  TokenKind::kDot,
      TokenKind::kColon,     TokenKind::kHash,   TokenKind::kAt,
  };
  ASSERT_EQ(tokens.size(), std::size(expected) + 1);
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(tokens[i].kind, expected[i]) << "token " << i;
  }
}

TEST(Lexer, Operators_Dollar) {
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(Lexer, Operators_MaximalMunch) {
  // §5.5: Triple-character operators are distinct from double+single.
  // "===" must lex as kEqEqEq, not kEqEq + kEq.
  auto tokens = Lex("===");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEqEqEq);
}

TEST(Lexer, Operators_UnaryAdjacentToOperand) {
  // §5.5: Unary operators to the left of their operand, no space required.
  auto tokens = Lex("~a !b");
  ASSERT_GE(tokens.size(), 5);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[1].text, "a");
  EXPECT_EQ(tokens[2].kind, TokenKind::kBang);
  EXPECT_EQ(tokens[3].text, "b");
}

TEST(Lexer, Operators_BinaryBetweenOperands) {
  // §5.5: Binary operators between operands.
  auto tokens = Lex("a + b");
  ASSERT_GE(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(Lexer, Operators_ConditionalTwoChars) {
  // §5.5: Conditional operator has two operator characters (? and :)
  // separating three operands.
  auto tokens = Lex("a ? b : c");
  ASSERT_GE(tokens.size(), 6);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kQuestion);
  EXPECT_EQ(tokens[2].text, "b");
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[4].text, "c");
}

TEST(Lexer, Operators_NoSpaceBetweenOperators) {
  // Operators adjacent to identifiers without whitespace.
  auto tokens = Lex("a+b*c");
  ASSERT_GE(tokens.size(), 6);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
  EXPECT_EQ(tokens[3].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[4].text, "c");
}

// --- §5.4: Comments ---

TEST(Lexer, Comment_LineComment) {
  auto tokens = Lex("a // comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_BlockComment) {
  auto tokens = Lex("a /* block */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_LineInsideBlock) {
  // §5.4: // has no special meaning inside /* */
  auto tokens = Lex("a /* // not a line comment */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_BlockInsideLine) {
  // §5.4: /* */ has no special meaning inside //
  auto tokens = Lex("a // /* not a block comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_MultilineBlock) {
  auto tokens = Lex("a /* line1\nline2\nline3 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_AdjacentComments) {
  auto tokens = Lex("a /* c1 */ /* c2 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_LineCommentAtEof) {
  auto tokens = Lex("a // trailing");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_TRUE(tokens[1].IsEof());
}

TEST(Lexer, Comment_EmptyBlockComment) {
  auto tokens = Lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_BlockNotNested) {
  // §5.4: "Block comments shall not be nested."
  // /* outer /* inner */ ends at first */ — "still_here" is a token.
  auto tokens = Lex("a /* outer /* inner */ still_here");
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "still_here");
}

TEST(Lexer, Comment_BlockNotNestedCloseStar) {
  // §5.4: Nested /* has no special meaning; first */ closes the comment.
  auto tokens = Lex("x /* a /* b */ y /* c */ z");
  ASSERT_GE(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "x");
  EXPECT_EQ(tokens[1].text, "y");
  // "/* c */" is a separate block comment
  EXPECT_EQ(tokens[2].text, "z");
}

TEST(Lexer, Comment_StarsInsideBlock) {
  // Stars that don't form */ should not end the block comment.
  auto tokens = Lex("a /* ** * *** */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_SlashesInsideBlock) {
  // Slashes inside block comment don't start new comments or end the block.
  auto tokens = Lex("a /* / // /// */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_LineCommentEndsAtNewline) {
  // §5.4: "A one-line comment shall start with // and end with a newline
  // character." — code on the next line is not part of the comment.
  auto tokens = Lex("a // comment text\nb // more\nc");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].text, "c");
}

TEST(Lexer, HelloSv) {
  auto tokens = Lex(
      "module hello;\n  initial $display(\"Hello, DeltaHDL!\");\nendmodule\n");
  struct Case {
    size_t idx;
    TokenKind kind;
    const char* text;
  };
  Case expected[] = {
      {0, TokenKind::kKwModule, nullptr},
      {1, TokenKind::kIdentifier, "hello"},
      {2, TokenKind::kSemicolon, nullptr},
      {3, TokenKind::kKwInitial, nullptr},
      {4, TokenKind::kSystemIdentifier, "$display"},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].kind, c.kind) << "token " << c.idx;
    if (c.text) {
      EXPECT_EQ(tokens[c.idx].text, c.text) << "token " << c.idx;
    }
  }
}

// --- §5.7.2: Real literal constants ---

TEST(Lexer, RealLiteral_FixedPoint) {
  auto tokens = Lex("3.14");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "3.14");
}

TEST(Lexer, RealLiteral_Exponent) {
  auto tokens = Lex("1e10");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1e10");
}

TEST(Lexer, RealLiteral_FixedExponent) {
  auto tokens = Lex("2.5e3");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "2.5e3");
}

TEST(Lexer, RealLiteral_LrmExamples) {
  // §5.7.2 examples: 1.2, 0.1, 2394.26331, 1.2E12, 1.30e-2, 0.1e-0,
  //                  23E10, 29E-2, 236.123_763_e-12
  for (const char* src : {"1.2", "0.1", "2394.26331", "1.2E12", "1.30e-2",
                          "0.1e-0", "23E10", "29E-2", "236.123_763_e-12"}) {
    auto tokens = Lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral) << src;
  }
}

TEST(Lexer, RealLiteral_NegativeExponent) {
  auto tokens = Lex("1.30e-2");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1.30e-2");
}

TEST(Lexer, RealLiteral_UppercaseE) {
  auto tokens = Lex("1.2E12");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1.2E12");
}

// --- §5.8: Time literals ---

TEST(Lexer, TimeLiteral_AllUnits) {
  // §5.8: time_unit ::= s | ms | us | ns | ps | fs
  for (const char* src : {"100s", "10ms", "5us", "100ns", "40ps", "1fs"}) {
    auto tokens = Lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral) << src;
  }
}

TEST(Lexer, TimeLiteral_LrmExamples) {
  // §5.8 examples: 2.1ns, 40ps
  auto t1 = Lex("2.1ns");
  EXPECT_EQ(t1[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t1[0].text, "2.1ns");
  auto t2 = Lex("40ps");
  EXPECT_EQ(t2[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t2[0].text, "40ps");
}

TEST(Lexer, TimeLiteral_FixedPointBase) {
  auto tokens = Lex("1.5us");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "1.5us");
}

TEST(Lexer, SourceLocations) {
  auto tokens = Lex("a\nb c");
  struct Case {
    size_t idx;
    int line;
    int column;
  };
  Case expected[] = {
      {0, 1, 1},
      {1, 2, 1},
      {2, 2, 3},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].loc.line, c.line) << "token " << c.idx;
    EXPECT_EQ(tokens[c.idx].loc.column, c.column) << "token " << c.idx;
  }
}

// --- §5.10/5.11: Assignment pattern token ---

TEST(Lexer, ApostropheLBrace) {
  auto tokens = Lex("'{0, 1}");
  ASSERT_GE(tokens.size(), 5);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[0].text, "'{");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, ApostropheLBraceNested) {
  auto tokens = Lex("'{'{1, 2}, '{3, 4}}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(Lexer, ApostropheLBrace_TypePrefixed) {
  // §5.10: ab'{int:1, shortreal:1.0} — type prefix then '{
  auto tokens = Lex("ab'{int:1}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "ab");
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(Lexer, ApostropheLBrace_Replication) {
  // §5.10: '{3{1}} — replication inside assignment pattern
  auto tokens = Lex("'{3{1}}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, ApostropheLBrace_ArrayLiteral) {
  // §5.11: '{'{0,1,2},'{3{4}}} — multi-dim array literal
  auto tokens = Lex("'{'{0,1,2},'{3{4}}}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, ApostropheLBrace_ArrayTypePrefixed) {
  // §5.11: triple'{0,1,2} — type-prefixed array literal
  auto tokens = Lex("triple'{0,1,2}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "triple");
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

// --- §5.12: Attribute tokens ---

TEST(Lexer, AttrStart) {
  auto tokens = Lex("(* full_case *)");
  ASSERT_GE(tokens.size(), 4);
  struct Case {
    size_t idx;
    TokenKind kind;
    const char* text;
  };
  Case expected[] = {
      {0, TokenKind::kAttrStart, "(*"},
      {1, TokenKind::kIdentifier, "full_case"},
      {2, TokenKind::kAttrEnd, "*)"},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].kind, c.kind) << "token " << c.idx;
    EXPECT_EQ(tokens[c.idx].text, c.text) << "token " << c.idx;
  }
}

TEST(Lexer, AttrWithValue) {
  // §5.12: (* attr_name = constant_expression *)
  auto tokens = Lex("(* synthesis = 1 *)");
  struct Case {
    size_t idx;
    TokenKind kind;
    const char* text;
  };
  Case expected[] = {
      {0, TokenKind::kAttrStart, nullptr},
      {1, TokenKind::kIdentifier, "synthesis"},
      {2, TokenKind::kEq, nullptr},
      {3, TokenKind::kIntLiteral, nullptr},
      {4, TokenKind::kAttrEnd, nullptr},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].kind, c.kind) << "token " << c.idx;
    if (c.text) {
      EXPECT_EQ(tokens[c.idx].text, c.text) << "token " << c.idx;
    }
  }
}

TEST(Lexer, AttrMultipleSpecs) {
  // §5.12: (* attr1, attr2 *)
  auto tokens = Lex("(* full_case, parallel_case *)");
  struct Case {
    size_t idx;
    TokenKind kind;
    const char* text;
  };
  Case expected[] = {
      {0, TokenKind::kAttrStart, nullptr},
      {1, TokenKind::kIdentifier, "full_case"},
      {2, TokenKind::kComma, nullptr},
      {3, TokenKind::kIdentifier, "parallel_case"},
      {4, TokenKind::kAttrEnd, nullptr},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].kind, c.kind) << "token " << c.idx;
    if (c.text) {
      EXPECT_EQ(tokens[c.idx].text, c.text) << "token " << c.idx;
    }
  }
}

TEST(Lexer, AttrDoesNotConfuseMultiply) {
  // (a * b) should NOT produce kAttrStart.
  auto tokens = Lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}
