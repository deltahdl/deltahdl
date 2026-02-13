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

TEST(Lexer, AllAnnexBKeywords) {
  // Every IEEE 1800-2023 Annex B keyword must lex as a keyword, not
  // kIdentifier.  If this test fails, a keyword is missing from the
  // keyword table in keywords.cpp or token.h.
  const char* const kKeywords[] = {
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
  for (const char* kw : kKeywords) {
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
  // §22.14: all nine version specifiers
  struct Case {
    const char* input;
    KeywordVersion expected;
  };
  const Case kCases[] = {
      {"1364-1995", KeywordVersion::kVer13641995},
      {"1364-2001", KeywordVersion::kVer13642001},
      {"1364-2001-noconfig", KeywordVersion::kVer13642001Noconfig},
      {"1364-2005", KeywordVersion::kVer13642005},
      {"1800-2005", KeywordVersion::kVer18002005},
      {"1800-2009", KeywordVersion::kVer18002009},
      {"1800-2012", KeywordVersion::kVer18002012},
      {"1800-2017", KeywordVersion::kVer18002017},
      {"1800-2023", KeywordVersion::kVer18002023},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(*ParseKeywordVersion(c.input), c.expected) << c.input;
  }
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
  for (const char* src : {"5 'D 3", "3'b01x", "12'hx", "16'hz"}) {
    auto tokens = lex(src);
    EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral) << src;
  }
}

TEST(Lexer, IntLiteral_LrmExample3_Signed) {
  // §5.7.1 Example 3: 4'shf, 16'sd?
  auto t1 = lex("4'shf");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  auto t2 = lex("16'sd?");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, IntLiteral_UnbasedUnsized) {
  // §5.7.1: '0, '1, 'x, 'X, 'z, 'Z are unbased unsized literals
  for (const char* src : {"'0", "'1", "'x", "'X", "'z", "'Z"}) {
    auto tokens = lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral) << src;
  }
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
  struct Case {
    const char* input;
    std::string expected;
  };
  const Case kCases[] = {
      {R"(hello\nworld)", "hello\nworld"},
      {R"(a\tb)", "a\tb"},
      {R"(a\\b)", "a\\b"},
      {R"(a\"b)", "a\"b"},
      {R"(a\vb)", std::string("a\vb")},
      {R"(a\fb)", std::string("a\fb")},
      {R"(a\ab)", std::string("a\ab")},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(InterpretStringEscapes(c.input), c.expected) << c.input;
  }
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

TEST(Lexer, InterpretEscapes_OctalMaxDigits) {
  using delta::InterpretStringEscapes;
  // §5.9.1: octal consumes up to 3 digits; \1019 → 'A' then '9'
  EXPECT_EQ(InterpretStringEscapes(R"(\1019)"), "A9");
}

TEST(Lexer, InterpretEscapes_TripleBackslashNewline) {
  using delta::InterpretStringEscapes;
  // §5.9.1: \\\<newline> → double backslash is escape for '\', then
  // backslash+newline is line continuation (both removed)
  EXPECT_EQ(InterpretStringEscapes("\\\\\\\n"), "\\");
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
