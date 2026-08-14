#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(UnpackedArrayParsing, UnpackedDimConstantRange) {
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

TEST(UnpackedArrayParsing, UnpackedDimConstantExpression) {
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

TEST(UnpackedArrayParsing, DataDeclUnpackedDimsInBlock) {
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

TEST(UnpackedArrayParsing, IntUnpackedDim) {
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

TEST(UnpackedArrayParsing, LogicUnpackedDim) {
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

TEST(UnpackedArrayParsing, UnpackedArrayRange) {
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

TEST(UnpackedArrayParsing, Int2DUnpackedArray) {
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

static bool ParseOk5(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

TEST(UnpackedArrayParsing, UnpackedDimMultiRange) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:2][1:3]; endmodule"));
}

TEST(UnpackedArrayParsing, RealUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  real vals [4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(UnpackedArrayParsing, StringUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  string names [3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// Covers the `msb : lsb` branch of Parser::ParseUnpackedDims in
// src/parser/parser_types.cpp, which builds an ExprKind::kBinary carrying the
// colon. It assigned no range.start before this commit, and
// src/parser/parser_types.cpp assigned none at any site, so a report standing
// at a declared dimension printed "<unknown location>" instead of a file, line
// and column. §7.4.2 writes the dimension as `[ constant_expression :
// constant_expression ]`, and the node holds the pair rather than the brackets,
// so it begins at its first bound: `3`, at column 10 of line 2.
TEST(UnpackedArrayParsing, UnpackedDimRangeStartsAtItsFirstBound) {
  auto r = Parse(
      "module m;\n"
      "  int u [3:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->kind, ExprKind::kBinary);
  EXPECT_EQ(dim->range.start.line, 2u);
  EXPECT_EQ(dim->range.start.column, 10u);
}

}  // namespace
