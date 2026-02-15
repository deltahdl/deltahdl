#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult28b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult28b Parse(const std::string& src) {
  ParseResult28b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 28.3.5 -- Primitives and strengths (range specification)
// =============================================================================

TEST(ParserSection28b, PrimitiveArrayOfInstances) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b, y;\n"
      "  and g[3:0] (y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, PrimitiveWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  nand (strong0, weak1) g1 (out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, PrimitiveWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire out;\n"
      "  and #(2, 3) g1 (out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, PrimitiveWithRangeAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] a, b, y;\n"
      "  nand #2 t_nand[0:7] (y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, MultiplePrimitiveInstances) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, y1, y2;\n"
      "  and g1 (y1, a, b), g2 (y2, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 27.3 -- Specify path declarations
// =============================================================================

TEST(ParserSection28b, SpecifyBlockSimplePath) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, SpecifyBlockParallelPath) {
  auto r = Parse(
      "module m(input a, b, output y);\n"
      "  assign y = a & b;\n"
      "  specify\n"
      "    (a => y) = 5;\n"
      "    (b => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, SpecifyBlockFullPath) {
  auto r = Parse(
      "module m(input a, b, output y, z);\n"
      "  assign y = a;\n"
      "  assign z = b;\n"
      "  specify\n"
      "    (a, b *> y, z) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection28b, SpecifyBlockWithTimingCheck) {
  auto r = Parse(
      "module m(input clk, d, output q);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, d, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
