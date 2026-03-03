#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// --- §5.7.1: Integer literal constants ---

TEST(LexerCh50701, NoDigitsAfterBaseError) {
  // §5.7.1: A plus or minus operator between the base format and the
  // number is illegal syntax.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'd-6");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(LexerCh50701, DecimalXZMixedError) {
  // §5.7.1: Decimal literal shall not contain x/z unless exactly one digit.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'd1x");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(LexerCh50701, DecimalXZMultiError) {
  // §5.7.1: Multiple x/z digits in decimal is invalid.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'dxz");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}
// ---------------------------------------------------------------------------
// 11. Sized hexadecimal literal constant
// ---------------------------------------------------------------------------
TEST(SimCh50701, SizedHexLiteral) {
  // §5.7.1: based literal with hex base
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 20'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

// ---------------------------------------------------------------------------
// 19. Left padding with zeros (value smaller than size)
// ---------------------------------------------------------------------------
TEST(SimCh50701, LeftPadWithZeros) {
  // §5.7.1: Value smaller than size — left-padded with zeros.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x0Fu);
}

// ---------------------------------------------------------------------------
// 34. White space between size and base format
// ---------------------------------------------------------------------------
TEST(SimCh50701, WhiteSpaceSizeAndBase) {
  // §5.7.1: White space allowed between size, base, and value tokens.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5 'd 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// 37. Size constant must be nonzero
// ---------------------------------------------------------------------------
TEST(SimCh50701, SizeConstantNonzero) {
  // §5.7.1: Size constant must be nonzero.
  // Using size=1 (the smallest legal size) verifies nonzero is accepted.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}

