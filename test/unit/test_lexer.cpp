#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

TEST(Lexer, EmptyInput) {
  auto tokens = lex("");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].IsEof());
}

// --- §5.3: White space ---

TEST(Lexer, Whitespace_SpaceSeparatesTokens) {
  auto tokens = lex("a b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_TabSeparatesTokens) {
  auto tokens = lex("a\tb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_NewlineSeparatesTokens) {
  auto tokens = lex("a\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_FormfeedSeparatesTokens) {
  auto tokens = lex("a\fb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_CarriageReturnSeparatesTokens) {
  auto tokens = lex("a\rb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_CrLfSeparatesTokens) {
  auto tokens = lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_MixedWhitespace) {
  auto tokens = lex("a \t\n \f b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Whitespace_LeadingAndTrailing) {
  auto tokens = lex("  \t a \n  ");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_TRUE(tokens[1].IsEof());
}

TEST(Lexer, Whitespace_OnlyWhitespace) {
  auto tokens = lex("   \t\n\f  ");
  ASSERT_EQ(tokens.size(), 1);
  EXPECT_TRUE(tokens[0].IsEof());
}

// --- §5.6.2: Keywords ---

TEST(Lexer, Keyword_Basic) {
  auto tokens = lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
  EXPECT_TRUE(tokens[2].IsEof());
}

TEST(Lexer, Keyword_LowercaseOnly) {
  // §5.6.2: keywords are lowercase only. Uppercase = identifier.
  auto tokens = lex("Module MODULE");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(Lexer, Keyword_EscapedKeywordIsIdentifier) {
  // §5.6.2: keyword preceded by backslash is not a keyword
  auto tokens = lex("\\module ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

// --- §5.6: Identifiers, keywords, and system names ---

TEST(Lexer, Identifier_SimpleLettersDigitsUnderscore) {
  auto tokens = lex("foo bar_123 _baz");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar_123");
  EXPECT_EQ(tokens[2].text, "_baz");
}

TEST(Lexer, Identifier_WithDollarSign) {
  // §5.6: $ is allowed in simple identifiers (but not first char)
  auto tokens = lex("n$657");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "n$657");
}

TEST(Lexer, Identifier_CaseSensitive) {
  // §5.6: identifiers are case sensitive
  auto tokens = lex("Foo foo FOO");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "Foo");
  EXPECT_EQ(tokens[1].text, "foo");
  EXPECT_EQ(tokens[2].text, "FOO");
  // All three are distinct identifiers
  EXPECT_NE(tokens[0].text, tokens[1].text);
}

TEST(Lexer, Identifier_UnderscoreStart) {
  // §5.6: first char can be underscore
  auto tokens = lex("_bus3");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_bus3");
}

TEST(Lexer, Identifier_LrmExamples) {
  // §5.6 examples: shiftreg_a, busa_index, error_condition, merge_ab
  for (const char* id :
       {"shiftreg_a", "busa_index", "error_condition", "merge_ab"}) {
    auto tokens = lex(id);
    ASSERT_GE(tokens.size(), 2) << id;
    EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier) << id;
    EXPECT_EQ(tokens[0].text, id) << id;
  }
}

// --- §5.7: Numbers (dispatch: integral vs real vs time) ---

TEST(Lexer, Number_IntegerLiterals) {
  auto tokens = lex("42 8'hFF 4'b1010");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "42");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].text, "8'hFF");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].text, "4'b1010");
}

TEST(Lexer, Number_DispatchIntRealTime) {
  // §5.7: number is integral_number or real_number; time_literal adds unit
  auto tokens = lex("42 3.14 100ns");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kTimeLiteral);
}

// --- §5.9: String literals ---

TEST(Lexer, String_Basic) {
  auto tokens = lex("\"Hello, World!\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"Hello, World!\"");
}

TEST(Lexer, String_Empty) {
  auto tokens = lex("\"\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"\"");
}

TEST(Lexer, String_WithEscapedQuote) {
  auto tokens = lex("\"say \\\"hi\\\"\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, String_WithEscapedBackslash) {
  auto tokens = lex("\"path\\\\dir\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, String_TripleQuotedWithUnescapedQuotes) {
  // §5.9: triple-quoted strings allow " without escape
  auto tokens = lex(R"("""a "quoted" word""")");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, String_TripleQuotedWithNewline) {
  // §5.9: triple-quoted strings allow direct newlines
  auto tokens = lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// --- §5.6.3: System tasks and system functions ---

TEST(Lexer, SystemTf_Basic) {
  auto tokens = lex("$display $finish");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].text, "$finish");
}

TEST(Lexer, SystemTf_EmbeddedDollar) {
  // §5.6.3: system_tf_identifier allows $ within the name
  auto tokens = lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(Lexer, SystemTf_WithDigitsAndUnderscore) {
  auto tokens = lex("$urandom_range $stime");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$urandom_range");
  EXPECT_EQ(tokens[1].text, "$stime");
}

TEST(Lexer, SystemTf_LrmExamples) {
  // §5.6.3 examples
  auto tokens = lex("$display $finish");
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
}

TEST(Lexer, SystemTf_DollarAloneIsNotSystem) {
  // Bare $ followed by non-alpha is just kDollar, not a system identifier
  auto tokens = lex("$");
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
  auto tokens = lex("+ - * / % & | ^ ~ ! = < > ?");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPercent);
  EXPECT_EQ(tokens[5].kind, TokenKind::kAmp);
  EXPECT_EQ(tokens[6].kind, TokenKind::kPipe);
  EXPECT_EQ(tokens[7].kind, TokenKind::kCaret);
  EXPECT_EQ(tokens[8].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[9].kind, TokenKind::kBang);
  EXPECT_EQ(tokens[10].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[11].kind, TokenKind::kLt);
  EXPECT_EQ(tokens[12].kind, TokenKind::kGt);
  EXPECT_EQ(tokens[13].kind, TokenKind::kQuestion);
}

TEST(Lexer, Operators_DoubleChar) {
  auto tokens =
      lex("== != <= >= << >> && || ** ++ -- -> => :: ~& ~| ~^ ^~ .* ## @@");
  EXPECT_EQ(tokens[0].kind, TokenKind::kEqEq);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kGtEq);
  EXPECT_EQ(tokens[4].kind, TokenKind::kLtLt);
  EXPECT_EQ(tokens[5].kind, TokenKind::kGtGt);
  EXPECT_EQ(tokens[6].kind, TokenKind::kAmpAmp);
  EXPECT_EQ(tokens[7].kind, TokenKind::kPipePipe);
  EXPECT_EQ(tokens[8].kind, TokenKind::kPower);
  EXPECT_EQ(tokens[9].kind, TokenKind::kPlusPlus);
  EXPECT_EQ(tokens[10].kind, TokenKind::kMinusMinus);
  EXPECT_EQ(tokens[11].kind, TokenKind::kArrow);
  EXPECT_EQ(tokens[12].kind, TokenKind::kEqGt);
  EXPECT_EQ(tokens[13].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[14].kind, TokenKind::kTildeAmp);
  EXPECT_EQ(tokens[15].kind, TokenKind::kTildePipe);
  EXPECT_EQ(tokens[16].kind, TokenKind::kTildeCaret);
  EXPECT_EQ(tokens[17].kind, TokenKind::kCaretTilde);
  EXPECT_EQ(tokens[18].kind, TokenKind::kDotStar);
  EXPECT_EQ(tokens[19].kind, TokenKind::kHashHash);
  EXPECT_EQ(tokens[20].kind, TokenKind::kAtAt);
}

TEST(Lexer, Operators_TripleChar) {
  auto tokens = lex("=== !== ==? !=? <<< >>> ->> |-> |=> <-> &&&");
  EXPECT_EQ(tokens[0].kind, TokenKind::kEqEqEq);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEqEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEqEqQuestion);
  EXPECT_EQ(tokens[3].kind, TokenKind::kBangEqQuestion);
  EXPECT_EQ(tokens[4].kind, TokenKind::kLtLtLt);
  EXPECT_EQ(tokens[5].kind, TokenKind::kGtGtGt);
  EXPECT_EQ(tokens[6].kind, TokenKind::kDashGtGt);
  EXPECT_EQ(tokens[7].kind, TokenKind::kPipeDashGt);
  EXPECT_EQ(tokens[8].kind, TokenKind::kPipeEqGt);
  EXPECT_EQ(tokens[9].kind, TokenKind::kLtDashGt);
  EXPECT_EQ(tokens[10].kind, TokenKind::kAmpAmpAmp);
}

TEST(Lexer, Operators_CompoundAssignment) {
  auto tokens = lex("+= -= *= /= %= &= |= ^= <<= >>= <<<= >>>=");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusEq);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStarEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlashEq);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPercentEq);
  EXPECT_EQ(tokens[5].kind, TokenKind::kAmpEq);
  EXPECT_EQ(tokens[6].kind, TokenKind::kPipeEq);
  EXPECT_EQ(tokens[7].kind, TokenKind::kCaretEq);
  EXPECT_EQ(tokens[8].kind, TokenKind::kLtLtEq);
  EXPECT_EQ(tokens[9].kind, TokenKind::kGtGtEq);
  EXPECT_EQ(tokens[10].kind, TokenKind::kLtLtLtEq);
  EXPECT_EQ(tokens[11].kind, TokenKind::kGtGtGtEq);
}

TEST(Lexer, Operators_IndexedPartSelect) {
  auto tokens = lex("+: -:");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusColon);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusColon);
}

TEST(Lexer, Operators_Tolerance) {
  auto tokens = lex("+/- +%-");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusSlashMinus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPercentMinus);
}

TEST(Lexer, Operators_StarGt) {
  auto tokens = lex("*>");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStarGt);
}

TEST(Lexer, Punctuation) {
  auto tokens = lex("( ) [ ] { } ; , . : # @");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRBracket);
  EXPECT_EQ(tokens[4].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[7].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[8].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[9].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[10].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[11].kind, TokenKind::kAt);
}

TEST(Lexer, Operators_Dollar) {
  auto tokens = lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

// --- §5.4: Comments ---

TEST(Lexer, Comment_LineComment) {
  auto tokens = lex("a // comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_BlockComment) {
  auto tokens = lex("a /* block */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_LineInsideBlock) {
  // §5.4: // has no special meaning inside /* */
  auto tokens = lex("a /* // not a line comment */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_BlockInsideLine) {
  // §5.4: /* */ has no special meaning inside //
  auto tokens = lex("a // /* not a block comment\nb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_MultilineBlock) {
  auto tokens = lex("a /* line1\nline2\nline3 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_AdjacentComments) {
  auto tokens = lex("a /* c1 */ /* c2 */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, Comment_LineCommentAtEof) {
  auto tokens = lex("a // trailing");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_TRUE(tokens[1].IsEof());
}

TEST(Lexer, Comment_EmptyBlockComment) {
  auto tokens = lex("a /**/ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(Lexer, HelloSv) {
  auto tokens = lex(
      "module hello;\n  initial $display(\"Hello, DeltaHDL!\");\nendmodule\n");
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "hello");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwInitial);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[4].text, "$display");
}

// --- §5.7.2: Real literal constants ---

TEST(Lexer, RealLiteral_FixedPoint) {
  auto tokens = lex("3.14");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "3.14");
}

TEST(Lexer, RealLiteral_Exponent) {
  auto tokens = lex("1e10");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1e10");
}

TEST(Lexer, RealLiteral_FixedExponent) {
  auto tokens = lex("2.5e3");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "2.5e3");
}

TEST(Lexer, RealLiteral_LrmExamples) {
  // §5.7.2 examples: 1.2, 0.1, 2394.26331, 1.2E12, 1.30e-2, 0.1e-0,
  //                  23E10, 29E-2, 236.123_763_e-12
  for (const char* src : {"1.2", "0.1", "2394.26331", "1.2E12", "1.30e-2",
                          "0.1e-0", "23E10", "29E-2", "236.123_763_e-12"}) {
    auto tokens = lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral) << src;
  }
}

TEST(Lexer, RealLiteral_NegativeExponent) {
  auto tokens = lex("1.30e-2");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1.30e-2");
}

TEST(Lexer, RealLiteral_UppercaseE) {
  auto tokens = lex("1.2E12");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1.2E12");
}

// --- §5.8: Time literals ---

TEST(Lexer, TimeLiteral_AllUnits) {
  // §5.8: time_unit ::= s | ms | us | ns | ps | fs
  for (const char* src : {"100s", "10ms", "5us", "100ns", "40ps", "1fs"}) {
    auto tokens = lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral) << src;
  }
}

TEST(Lexer, TimeLiteral_LrmExamples) {
  // §5.8 examples: 2.1ns, 40ps
  auto t1 = lex("2.1ns");
  EXPECT_EQ(t1[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t1[0].text, "2.1ns");
  auto t2 = lex("40ps");
  EXPECT_EQ(t2[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t2[0].text, "40ps");
}

TEST(Lexer, TimeLiteral_FixedPointBase) {
  auto tokens = lex("1.5us");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "1.5us");
}

TEST(Lexer, SourceLocations) {
  auto tokens = lex("a\nb c");
  EXPECT_EQ(tokens[0].loc.line, 1);
  EXPECT_EQ(tokens[0].loc.column, 1);
  EXPECT_EQ(tokens[1].loc.line, 2);
  EXPECT_EQ(tokens[1].loc.column, 1);
  EXPECT_EQ(tokens[2].loc.line, 2);
  EXPECT_EQ(tokens[2].loc.column, 3);
}

// --- §5.10/5.11: Assignment pattern token ---

TEST(Lexer, ApostropheLBrace) {
  auto tokens = lex("'{0, 1}");
  ASSERT_GE(tokens.size(), 5);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[0].text, "'{");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, ApostropheLBraceNested) {
  auto tokens = lex("'{'{1, 2}, '{3, 4}}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(Lexer, ApostropheLBrace_TypePrefixed) {
  // §5.10: ab'{int:1, shortreal:1.0} — type prefix then '{
  auto tokens = lex("ab'{int:1}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "ab");
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(Lexer, ApostropheLBrace_Replication) {
  // §5.10: '{3{1}} — replication inside assignment pattern
  auto tokens = lex("'{3{1}}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, ApostropheLBrace_ArrayLiteral) {
  // §5.11: '{'{0,1,2},'{3{4}}} — multi-dim array literal
  auto tokens = lex("'{'{0,1,2},'{3{4}}}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, ApostropheLBrace_ArrayTypePrefixed) {
  // §5.11: triple'{0,1,2} — type-prefixed array literal
  auto tokens = lex("triple'{0,1,2}");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "triple");
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

// --- §5.12: Attribute tokens ---

TEST(Lexer, AttrStart) {
  auto tokens = lex("(* full_case *)");
  ASSERT_GE(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[0].text, "(*");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "full_case");
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
  EXPECT_EQ(tokens[2].text, "*)");
}

TEST(Lexer, AttrWithValue) {
  // §5.12: (* attr_name = constant_expression *)
  auto tokens = lex("(* synthesis = 1 *)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "synthesis");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(Lexer, AttrMultipleSpecs) {
  // §5.12: (* attr1, attr2 *)
  auto tokens = lex("(* full_case, parallel_case *)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "full_case");
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "parallel_case");
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(Lexer, AttrDoesNotConfuseMultiply) {
  // (a * b) should NOT produce kAttrStart.
  auto tokens = lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}
