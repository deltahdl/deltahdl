// §20.7: Array query functions

#include "fixture_parser.h"

using namespace delta;

struct ParseResult7b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static Stmt* FirstInitialStmt(ParseResult7b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// --- Test helpers ---
struct ParseResult7c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7c Parse(const std::string& src) {
  ParseResult7c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =========================================================================
// §7.11: Array querying functions
// =========================================================================
TEST(ParserSection7, ArrayDimensionsQuery) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4][8];\n"
      "  initial x = $dimensions(arr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$dimensions");
}

TEST(ParserSection7, ArraySizeQuery) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = $size(arr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$size");
}

struct ParseResult21 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult21 Parse(const std::string& src) {
  ParseResult21 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// LRM section 20.7 -- Array querying functions
// =============================================================================
TEST(ParserSection20, ArrayLeftFunction) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] mem [0:255];\n"
      "  initial begin\n"
      "    $display(\"high=%0d low=%0d\", $high(mem), $low(mem));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, ArrayDimensionsFunction) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $size(mem, 2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
