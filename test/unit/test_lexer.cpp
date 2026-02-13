#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "lexer/string_escape.h"

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

TEST(Lexer, StringLiterals) {
  auto tokens = lex("\"Hello, World!\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"Hello, World!\"");
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

TEST(Lexer, RealLiteralFixed) {
  auto tokens = lex("3.14");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "3.14");
}

TEST(Lexer, RealLiteralExponent) {
  auto tokens = lex("1e10");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1e10");
}

TEST(Lexer, RealLiteralFixedExponent) {
  auto tokens = lex("2.5e3");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "2.5e3");
}

TEST(Lexer, TimeLiteral) {
  auto tokens = lex("100ns");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "100ns");
}

TEST(Lexer, TimeLiteralMs) {
  auto tokens = lex("10ms");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[0].text, "10ms");
}

TEST(Lexer, TimeLiteralRealBase) {
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

TEST(Lexer, AttrDoesNotConfuseMultiply) {
  // (a * b) should NOT produce kAttrStart.
  auto tokens = lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

TEST(Lexer, AllAnnexBKeywords) {
  // Every IEEE 1800-2023 Annex B keyword must lex as a keyword, not
  // kIdentifier.  If this test fails, a keyword is missing from the
  // keyword table in keywords.cpp or token.h.
  const char* keywords[] = {
      "accept_on",
      "alias",
      "always",
      "always_comb",
      "always_ff",
      "always_latch",
      "and",
      "assert",
      "assign",
      "assume",
      "automatic",
      "before",
      "begin",
      "bind",
      "bins",
      "binsof",
      "bit",
      "break",
      "buf",
      "bufif0",
      "bufif1",
      "byte",
      "case",
      "casex",
      "casez",
      "cell",
      "chandle",
      "checker",
      "class",
      "clocking",
      "cmos",
      "config",
      "const",
      "constraint",
      "context",
      "continue",
      "cover",
      "covergroup",
      "coverpoint",
      "cross",
      "deassign",
      "default",
      "defparam",
      "design",
      "disable",
      "dist",
      "do",
      "edge",
      "else",
      "end",
      "endcase",
      "endchecker",
      "endclass",
      "endclocking",
      "endconfig",
      "endfunction",
      "endgenerate",
      "endgroup",
      "endinterface",
      "endmodule",
      "endpackage",
      "endprimitive",
      "endprogram",
      "endproperty",
      "endspecify",
      "endsequence",
      "endtable",
      "endtask",
      "enum",
      "event",
      "eventually",
      "expect",
      "export",
      "extends",
      "extern",
      "final",
      "first_match",
      "for",
      "force",
      "foreach",
      "forever",
      "fork",
      "forkjoin",
      "function",
      "generate",
      "genvar",
      "global",
      "highz0",
      "highz1",
      "if",
      "iff",
      "ifnone",
      "ignore_bins",
      "illegal_bins",
      "implements",
      "implies",
      "import",
      "incdir",
      "include",
      "initial",
      "inout",
      "input",
      "inside",
      "instance",
      "int",
      "integer",
      "interconnect",
      "interface",
      "intersect",
      "join",
      "join_any",
      "join_none",
      "large",
      "let",
      "liblist",
      "library",
      "local",
      "localparam",
      "logic",
      "longint",
      "macromodule",
      "matches",
      "medium",
      "modport",
      "module",
      "nand",
      "negedge",
      "nettype",
      "new",
      "nexttime",
      "nmos",
      "nor",
      "noshowcancelled",
      "not",
      "notif0",
      "notif1",
      "null",
      "or",
      "output",
      "package",
      "packed",
      "parameter",
      "pmos",
      "posedge",
      "primitive",
      "priority",
      "program",
      "property",
      "protected",
      "pull0",
      "pull1",
      "pulldown",
      "pullup",
      "pulsestyle_ondetect",
      "pulsestyle_onevent",
      "pure",
      "rand",
      "randc",
      "randcase",
      "randsequence",
      "rcmos",
      "real",
      "realtime",
      "ref",
      "reg",
      "reject_on",
      "release",
      "repeat",
      "restrict",
      "return",
      "rnmos",
      "rpmos",
      "rtran",
      "rtranif0",
      "rtranif1",
      "s_always",
      "s_eventually",
      "s_nexttime",
      "s_until",
      "s_until_with",
      "scalared",
      "sequence",
      "shortint",
      "shortreal",
      "showcancelled",
      "signed",
      "small",
      "soft",
      "solve",
      "specify",
      "specparam",
      "static",
      "string",
      "strong",
      "strong0",
      "strong1",
      "struct",
      "super",
      "supply0",
      "supply1",
      "sync_accept_on",
      "sync_reject_on",
      "table",
      "tagged",
      "task",
      "this",
      "throughout",
      "time",
      "timeprecision",
      "timeunit",
      "tran",
      "tranif0",
      "tranif1",
      "tri",
      "tri0",
      "tri1",
      "triand",
      "trior",
      "trireg",
      "type",
      "typedef",
      "union",
      "unique",
      "unique0",
      "unsigned",
      "until",
      "until_with",
      "untyped",
      "use",
      "uwire",
      "var",
      "vectored",
      "virtual",
      "void",
      "wait",
      "wait_order",
      "wand",
      "weak",
      "weak0",
      "weak1",
      "while",
      "wildcard",
      "wire",
      "with",
      "within",
      "wor",
      "xnor",
      "xor",
  };
  for (const char* kw : keywords) {
    auto tokens = lex(kw);
    ASSERT_GE(tokens.size(), 2) << "keyword: " << kw;
    EXPECT_NE(tokens[0].kind, TokenKind::kIdentifier)
        << kw << " should be a keyword, not an identifier";
  }
}

// --- Keyword version tests (IEEE 1800-2023 §22.14) ---

TEST(Lexer, KeywordVersion_1364_2001_LogicIsIdentifier) {
  // "logic" was introduced in 1800-2005, not a keyword in 1364-2001.
  auto kw = LookupKeyword("logic", KeywordVersion::kVer13642001);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersion_1800_2005_LogicIsKeyword) {
  auto kw = LookupKeyword("logic", KeywordVersion::kVer18002005);
  ASSERT_TRUE(kw.has_value());
  EXPECT_EQ(*kw, TokenKind::kKwLogic);
}

TEST(Lexer, KeywordVersion_Noconfig_ExcludesConfigKeywords) {
  // "config" was added in 1364-2001 but excluded by noconfig.
  auto kw = LookupKeyword("config", KeywordVersion::kVer13642001Noconfig);
  EXPECT_FALSE(kw.has_value());
  // "generate" was also added in 1364-2001 and NOT excluded.
  auto gen = LookupKeyword("generate", KeywordVersion::kVer13642001Noconfig);
  EXPECT_TRUE(gen.has_value());
}

TEST(Lexer, KeywordVersion_1364_1995_ModuleIsKeyword) {
  auto kw = LookupKeyword("module", KeywordVersion::kVer13641995);
  ASSERT_TRUE(kw.has_value());
  EXPECT_EQ(*kw, TokenKind::kKwModule);
}

TEST(Lexer, KeywordVersion_1364_1995_AutomaticIsNotKeyword) {
  // "automatic" was introduced in 1364-2001.
  auto kw = LookupKeyword("automatic", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersionMarker_SwitchesVersion) {
  // Build input: marker for 1364-2001, then "logic".
  // The lexer should tokenize "logic" as an identifier, not a keyword.
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13642001));
  input += '\n';
  input += "logic";
  auto tokens = lex(input);
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "logic");
}

TEST(Lexer, KeywordVersionMarker_RestoresToDefault) {
  // marker 1364-2001, "logic", marker 1800-2023, "logic"
  std::string input;
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer13642001));
  input += '\n';
  input += "logic ";
  input += kKeywordMarker;
  input +=
      static_cast<char>(static_cast<uint8_t>(KeywordVersion::kVer18002023));
  input += '\n';
  input += "logic";
  auto tokens = lex(input);
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwLogic);
}

TEST(Lexer, ParseKeywordVersion_ValidVersions) {
  EXPECT_EQ(*ParseKeywordVersion("1364-1995"), KeywordVersion::kVer13641995);
  EXPECT_EQ(*ParseKeywordVersion("1364-2001"), KeywordVersion::kVer13642001);
  EXPECT_EQ(*ParseKeywordVersion("1800-2023"), KeywordVersion::kVer18002023);
}

TEST(Lexer, ParseKeywordVersion_Invalid) {
  EXPECT_FALSE(ParseKeywordVersion("bogus").has_value());
  EXPECT_FALSE(ParseKeywordVersion("").has_value());
}

// --- §5.7.1: Integer literal constants ---

TEST(Lexer, IntLiteral_LrmExample1_Unsized) {
  // §5.7.1 Example 1: 659, 'h 837FF, 'o7460
  auto t1 = lex("659");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(t1[0].text, "659");
  auto t2 = lex("'h 837FF");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
  auto t3 = lex("'o7460");
  EXPECT_EQ(t3[0].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, IntLiteral_LrmExample2_Sized) {
  // §5.7.1 Example 2: 4'b1001, 5 'D 3, 3'b01x, 12'hx, 16'hz
  auto t1 = lex("4'b1001");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(t1[0].text, "4'b1001");
  auto t2 = lex("5 'D 3");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
  auto t3 = lex("3'b01x");
  EXPECT_EQ(t3[0].kind, TokenKind::kIntLiteral);
  auto t4 = lex("12'hx");
  EXPECT_EQ(t4[0].kind, TokenKind::kIntLiteral);
  auto t5 = lex("16'hz");
  EXPECT_EQ(t5[0].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, IntLiteral_LrmExample3_Signed) {
  // §5.7.1 Example 3: 4'shf, 16'sd?
  auto t1 = lex("4'shf");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  auto t2 = lex("16'sd?");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, IntLiteral_LrmExample6_Underscores) {
  // §5.7.1 Example 6: 27_195_000, 16'b0011_0101_0001_1111
  auto t1 = lex("27_195_000");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(t1[0].text, "27_195_000");
  auto t2 = lex("16'b0011_0101_0001_1111");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
}

// --- Whitespace in numeric literals (§5.7.1) ---

TEST(Lexer, SpaceBeforeBase_SizedHex) {
  auto tokens = lex("32 'h 12ab_f001");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "32 'h 12ab_f001");
}

TEST(Lexer, SpaceAfterBase_UnsizedHex) {
  auto tokens = lex("'h 837FF");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "'h 837FF");
}

TEST(Lexer, SpaceAfterBase_HexXZ) {
  auto tokens = lex("'h x");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "'h x");
}

TEST(Lexer, NoSpace_SizedHexStillWorks) {
  auto tokens = lex("32'hFF");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "32'hFF");
}

TEST(Lexer, SpaceAfterBase_SignedDecimal) {
  auto tokens = lex("8'd 6");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8'd 6");
}

// --- Reject negative after base (§5.7.1) ---

TEST(Lexer, BasedNumber_NoDigitsAfterBase_Error) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'd-6");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();  // lex the based number
  EXPECT_TRUE(diag.HasErrors());
}

// --- Triple-quoted strings (§5.9) ---

TEST(Lexer, TripleQuotedString_Basic) {
  auto tokens = lex(R"("""hello""")");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, R"("""hello""")");
}

TEST(Lexer, TripleQuotedString_WithNewline) {
  auto tokens = lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, TripleQuotedString_WithQuote) {
  auto tokens = lex(R"("""a "quoted" word""")");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, TripleQuotedString_WithEscape) {
  auto tokens = lex(R"("""hello\nworld""")");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

// --- §5.9.1: String escape sequence interpretation ---

TEST(Lexer, InterpretEscapes_NamedChars) {
  using delta::InterpretStringEscapes;
  EXPECT_EQ(InterpretStringEscapes(R"(hello\nworld)"), "hello\nworld");
  EXPECT_EQ(InterpretStringEscapes(R"(a\tb)"), "a\tb");
  EXPECT_EQ(InterpretStringEscapes(R"(a\\b)"), "a\\b");
  EXPECT_EQ(InterpretStringEscapes(R"(a\"b)"), "a\"b");
  EXPECT_EQ(InterpretStringEscapes(R"(a\vb)"), std::string("a\vb"));
  EXPECT_EQ(InterpretStringEscapes(R"(a\fb)"), std::string("a\fb"));
  EXPECT_EQ(InterpretStringEscapes(R"(a\ab)"), std::string("a\ab"));
}

TEST(Lexer, InterpretEscapes_Octal) {
  using delta::InterpretStringEscapes;
  EXPECT_EQ(InterpretStringEscapes(R"(\101)"), "A");      // 0101 = 65 = 'A'
  EXPECT_EQ(InterpretStringEscapes(R"(\12)"), "\n");      // 012 = 10 = newline
  EXPECT_EQ(InterpretStringEscapes(R"(\7)"), "\a");       // 07 = 7 = bell
  EXPECT_EQ(InterpretStringEscapes(R"(\101BC)"), "ABC");  // \101 then BC
}

TEST(Lexer, InterpretEscapes_Hex) {
  using delta::InterpretStringEscapes;
  EXPECT_EQ(InterpretStringEscapes(R"(\x41)"), "A");   // 0x41 = 65 = 'A'
  EXPECT_EQ(InterpretStringEscapes(R"(\x0A)"), "\n");  // 0x0A = newline
  EXPECT_EQ(InterpretStringEscapes(R"(\xAhello)"),
            "\nhello");  // single hex digit
}

TEST(Lexer, InterpretEscapes_Unknown) {
  using delta::InterpretStringEscapes;
  // Unknown escape: treated as if not escaped (§5.9.1)
  EXPECT_EQ(InterpretStringEscapes(R"(\b)"), "b");
  EXPECT_EQ(InterpretStringEscapes(R"(\q)"), "q");
}

TEST(Lexer, InterpretEscapes_LineContinuation) {
  using delta::InterpretStringEscapes;
  // §5.9: backslash + newline → both ignored (line continuation)
  EXPECT_EQ(InterpretStringEscapes("hello\\\nworld"), "helloworld");
  // Windows line endings
  EXPECT_EQ(InterpretStringEscapes("hello\\\r\nworld"), "helloworld");
}

TEST(Lexer, InterpretEscapes_NoEscapes) {
  using delta::InterpretStringEscapes;
  EXPECT_EQ(InterpretStringEscapes("hello world"), "hello world");
  EXPECT_EQ(InterpretStringEscapes(""), "");
}

// --- §5.6.1: Escaped identifiers ---

TEST(Lexer, EscapedIdentifier_Basic) {
  auto tokens = lex("\\my+name ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\my+name");
}

TEST(Lexer, EscapedIdentifier_SpecialChars) {
  // §5.6.1: printable ASCII 33-126 allowed
  auto tokens = lex("\\busa+index ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\busa+index");
}

TEST(Lexer, EscapedIdentifier_LrmExamples) {
  // §5.6.1 examples
  for (const char* src :
       {"\\busa+index ", "\\-clock ", "\\***error-condition*** ", "\\{a,b} ",
        "\\a*(b+c) "}) {
    auto tokens = lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier) << src;
  }
}

TEST(Lexer, EscapedIdentifier_KeywordBecomesIdentifier) {
  // §5.6.1: \net is a user-defined identifier, not the keyword "net"
  auto tokens = lex("\\net ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\net");
}

TEST(Lexer, EscapedIdentifier_TerminatedBySpace) {
  auto tokens = lex("\\esc_id next");
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
  EXPECT_EQ(tokens[1].text, "next");
}

TEST(Lexer, EscapedIdentifier_TerminatedByNewline) {
  auto tokens = lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(Lexer, EscapedIdentifier_TerminatedByTab) {
  auto tokens = lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

// --- §5.6: Identifier max length validation ---

TEST(Lexer, IdentifierMaxLength_Ok) {
  std::string id(1024, 'a');
  auto tokens = lex(id);
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(Lexer, IdentifierMaxLength_Error) {
  std::string id(1025, 'a');
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", id);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(Lexer, EscapedIdentifierMaxLength_Error) {
  std::string id = "\\" + std::string(1025, 'a') + " ";
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", id);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(Lexer, UnterminatedBlockComment_Error) {
  std::string src = "/* no end";
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

// --- §5.9: Unterminated triple-quoted string ---

TEST(Lexer, UnterminatedTripleQuotedString_Error) {
  std::string src = R"("""no closing triple)";
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

// --- §5.7.1: Decimal x/z validation ---

TEST(Lexer, DecimalXZ_SingleDigit_Valid) {
  // 8'dx, 8'dz, 8'd? — single x/z/? is valid (all bits)
  for (const char* src : {"8'dx", "8'dz", "8'd?"}) {
    SourceManager mgr;
    DiagEngine diag(mgr);
    auto fid = mgr.AddFile("<test>", src);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    lexer.LexAll();
    EXPECT_FALSE(diag.HasErrors()) << "should be valid: " << src;
  }
}

TEST(Lexer, DecimalXZ_Mixed_Error) {
  // 8'd1x — mixed decimal digits with x/z/? is invalid
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'd1x");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(Lexer, DecimalXZ_MultiXZ_Error) {
  // 8'dxz — multiple x/z digits in decimal is invalid
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'dxz");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}
