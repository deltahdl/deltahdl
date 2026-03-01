// §7.4.2: Unpacked arrays

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, VarDeclAssignmentWithDims) {
  auto r = Parse("module m; int arr [3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "arr");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

// =============================================================================
// A.2.5 Declaration ranges
// =============================================================================
// ---------------------------------------------------------------------------
// unpacked_dimension ::= [ constant_range ] | [ constant_expression ]
// ---------------------------------------------------------------------------
TEST(ParserA25, UnpackedDimConstantRange) {
  auto r = Parse("module m; logic x [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kColon);
}

TEST(ParserA25, UnpackedDimConstantExpression) {
  auto r = Parse("module m; logic x [8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserA28, DataDeclUnpackedDimsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int arr[3];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_unpacked_dims.size(), 1u);
}

struct ParseResult6h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6h Parse(const std::string& src) {
  ParseResult6h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6h& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// 3. Unpacked dimensions on int type (fixed-size array).
TEST(ParserSection6, Sec6_11_IntUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  int arr[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6j& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// 9. Logic with unpacked dimension [4].
TEST(ParserSection6, Sec6_5_LogicUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  logic arr [4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FirstItem(ParseResult7& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =========================================================================
// §7.4: Packed and unpacked arrays
// =========================================================================
TEST(ParserSection7, UnpackedArraySize) {
  auto r = Parse(
      "module t;\n"
      "  int arr[8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, UnpackedArrayRange) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem[0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

struct ParseResult7b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ModuleItem* FirstItem(ParseResult7b& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
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

TEST(ParserSection7, UnpackedArrayFixedSize) {
  auto r = Parse(
      "module t;\n"
      "  int arr [3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// 18. Integer types with 2D unpacked arrays.
TEST(ParserSection6, Sec6_11_Int2DUnpackedArray) {
  auto r = Parse(
      "module t;\n"
      "  int matrix[3][4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "matrix");
  ASSERT_GE(item->unpacked_dims.size(), 2u);
}

}  // namespace
