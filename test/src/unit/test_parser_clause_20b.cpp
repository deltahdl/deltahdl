#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult20b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult20b Parse(const std::string &src) {
  ParseResult20b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 20.6.3 -- $isunbounded (range system function)
// =============================================================================

TEST(ParserSection20, IsUnboundedBasic) {
  auto r = Parse("module m #(parameter int P = $);\n"
                 "  initial begin\n"
                 "    if ($isunbounded(P)) $display(\"unbounded\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, IsUnboundedInConditional) {
  auto r = Parse("module m #(parameter int N = $);\n"
                 "  generate\n"
                 "    if (!$isunbounded(N)) begin\n"
                 "      assign out = in;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, IsUnboundedWithBoundedParam) {
  auto r = Parse("module m #(parameter int P = 42);\n"
                 "  initial begin\n"
                 "    if ($isunbounded(P)) $display(\"yes\");\n"
                 "    else $display(\"no\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 20.7 -- Array querying functions
// =============================================================================

TEST(ParserSection20, ArrayLeftFunction) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] arr;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = $left(arr);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayRightFunction) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] arr;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = $right(arr);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArraySizeFunction) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] arr [16];\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = $size(arr);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayHighLowFunctions) {
  auto r = Parse("module m;\n"
                 "  logic [15:0] mem [0:255];\n"
                 "  initial begin\n"
                 "    $display(\"high=%0d low=%0d\", $high(mem), $low(mem));\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayDimensionsFunction) {
  auto r = Parse("module m;\n"
                 "  logic [3:0][7:0] data;\n"
                 "  initial begin\n"
                 "    int d;\n"
                 "    d = $dimensions(data);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayIncrementFunction) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] arr;\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = $increment(arr);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArraySizeWithDimArg) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] mem [0:15];\n"
                 "  initial begin\n"
                 "    int x;\n"
                 "    x = $size(mem, 2);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayUnpackedDimensionsFunction) {
  auto r = Parse("module m;\n"
                 "  logic arr [4][8];\n"
                 "  initial begin\n"
                 "    int d;\n"
                 "    d = $unpacked_dimensions(arr);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
