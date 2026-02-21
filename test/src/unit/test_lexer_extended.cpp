#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "lexer/string_escape.h"

using namespace delta;

static std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

// --- §5.7.1: Integer literal constants ---

TEST(Lexer, IntLiteral_LrmExample1_Unsized) {
  // §5.7.1 Example 1: 659, 'h 837FF, 'o7460
  auto t1 = Lex("659");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(t1[0].text, "659");
  auto t2 = Lex("'h 837FF");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
  auto t3 = Lex("'o7460");
  EXPECT_EQ(t3[0].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, IntLiteral_LrmExample2_Sized) {
  // §5.7.1 Example 2: 4'b1001, 5 'D 3, 3'b01x, 12'hx, 16'hz
  auto t1 = Lex("4'b1001");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(t1[0].text, "4'b1001");
  for (const char* src : {"5 'D 3", "3'b01x", "12'hx", "16'hz"}) {
    auto tokens = Lex(src);
    EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral) << src;
  }
}

TEST(Lexer, IntLiteral_LrmExample3_Signed) {
  // §5.7.1 Example 3: 4'shf, 16'sd?
  auto t1 = Lex("4'shf");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  auto t2 = Lex("16'sd?");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
}

TEST(Lexer, IntLiteral_UnbasedUnsized) {
  // §5.7.1: '0, '1, 'x, 'X, 'z, 'Z are unbased unsized literals
  for (const char* src : {"'0", "'1", "'x", "'X", "'z", "'Z"}) {
    auto tokens = Lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral) << src;
  }
}

TEST(Lexer, IntLiteral_LrmExample6_Underscores) {
  // §5.7.1 Example 6: 27_195_000, 16'b0011_0101_0001_1111
  auto t1 = Lex("27_195_000");
  EXPECT_EQ(t1[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(t1[0].text, "27_195_000");
  auto t2 = Lex("16'b0011_0101_0001_1111");
  EXPECT_EQ(t2[0].kind, TokenKind::kIntLiteral);
}

// --- Whitespace in numeric literals (§5.7.1) ---

TEST(Lexer, SpaceBeforeBase_SizedHex) {
  auto tokens = Lex("32 'h 12ab_f001");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "32 'h 12ab_f001");
}

TEST(Lexer, SpaceAfterBase_UnsizedHex) {
  auto tokens = Lex("'h 837FF");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "'h 837FF");
}

TEST(Lexer, SpaceAfterBase_HexXZ) {
  auto tokens = Lex("'h x");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "'h x");
}

TEST(Lexer, NoSpace_SizedHexStillWorks) {
  auto tokens = Lex("32'hFF");
  ASSERT_GE(tokens.size(), 1);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "32'hFF");
}

TEST(Lexer, SpaceAfterBase_SignedDecimal) {
  auto tokens = Lex("8'd 6");
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
  auto tokens = Lex(R"("""hello""")");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, R"("""hello""")");
}

TEST(Lexer, TripleQuotedString_WithNewline) {
  auto tokens = Lex("\"\"\"line1\nline2\"\"\"");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, TripleQuotedString_WithQuote) {
  auto tokens = Lex(R"("""a "quoted" word""")");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
}

TEST(Lexer, TripleQuotedString_WithEscape) {
  auto tokens = Lex(R"("""hello\nworld""")");
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
  auto tokens = Lex("\\my+name ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\my+name");
}

TEST(Lexer, EscapedIdentifier_SpecialChars) {
  // §5.6.1: printable ASCII 33-126 allowed
  auto tokens = Lex("\\busa+index ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\busa+index");
}

TEST(Lexer, EscapedIdentifier_LrmExamples) {
  // §5.6.1 examples
  for (const char* src :
       {"\\busa+index ", "\\-clock ", "\\***error-condition*** ", "\\{a,b} ",
        "\\a*(b+c) "}) {
    auto tokens = Lex(src);
    ASSERT_GE(tokens.size(), 2) << src;
    EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier) << src;
  }
}

TEST(Lexer, EscapedIdentifier_KeywordBecomesIdentifier) {
  // §5.6.1: \net is a user-defined identifier, not the keyword "net"
  auto tokens = Lex("\\net ");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\net");
}

TEST(Lexer, EscapedIdentifier_TerminatedBySpace) {
  auto tokens = Lex("\\esc_id next");
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
  EXPECT_EQ(tokens[1].text, "next");
}

TEST(Lexer, EscapedIdentifier_TerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(Lexer, EscapedIdentifier_TerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

// --- §5.6: Identifier max length validation ---

TEST(Lexer, IdentifierMaxLength_Ok) {
  std::string id(1024, 'a');
  auto tokens = Lex(id);
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
