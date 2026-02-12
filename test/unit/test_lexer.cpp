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

TEST(Lexer, Keywords) {
  auto tokens = lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
  EXPECT_TRUE(tokens[2].IsEof());
}

TEST(Lexer, Identifiers) {
  auto tokens = lex("foo bar_123 _baz");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar_123");
  EXPECT_EQ(tokens[2].text, "_baz");
}

TEST(Lexer, IntegerLiterals) {
  auto tokens = lex("42 8'hFF 4'b1010");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "42");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].text, "8'hFF");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].text, "4'b1010");
}

TEST(Lexer, StringLiterals) {
  auto tokens = lex("\"Hello, World!\"");
  ASSERT_EQ(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"Hello, World!\"");
}

TEST(Lexer, SystemIdentifiers) {
  auto tokens = lex("$display $finish");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].text, "$finish");
}

TEST(Lexer, EmbeddedDollarSystemIdentifiers) {
  auto tokens = lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(Lexer, Operators) {
  auto tokens = lex("+ - * / == != <= >= << >> && ||");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[4].kind, TokenKind::kEqEq);
  EXPECT_EQ(tokens[5].kind, TokenKind::kBangEq);
  EXPECT_EQ(tokens[6].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[7].kind, TokenKind::kGtEq);
  EXPECT_EQ(tokens[8].kind, TokenKind::kLtLt);
  EXPECT_EQ(tokens[9].kind, TokenKind::kGtGt);
  EXPECT_EQ(tokens[10].kind, TokenKind::kAmpAmp);
  EXPECT_EQ(tokens[11].kind, TokenKind::kPipePipe);
}

TEST(Lexer, Punctuation) {
  auto tokens = lex("( ) [ ] { } ; , . :");
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
}

TEST(Lexer, SkipsComments) {
  auto tokens = lex("a // comment\nb /* block */ c");
  ASSERT_EQ(tokens.size(), 4);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].text, "c");
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
