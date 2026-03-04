// §7.4.2: Unpacked arrays

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA24, VarDeclAssignmentWithDims) {
  auto r = Parse("module m; int arr [3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserA28, DataDeclUnpackedDimsInBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    int arr[3];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_unpacked_dims.size(), 1u);
}
// 3. Unpacked dimensions on int type (fixed-size array).
TEST(ParserSection6, Sec6_11_IntUnpackedDim) {
  auto r = Parse("module t;\n"
                 "  int arr[5];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}
// 9. Logic with unpacked dimension [4].
TEST(ParserSection6, Sec6_5_LogicUnpackedDim) {
  auto r = Parse("module t;\n"
                 "  logic arr [4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}
// =========================================================================
// §7.4: Packed and unpacked arrays
// =========================================================================
TEST(ParserSection7, UnpackedArraySize) {
  auto r = Parse("module t;\n"
                 "  int arr[8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, UnpackedArrayRange) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] mem[0:255];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->unpacked_dims.empty());
}
// --- Test helpers ---
TEST(ParserSection7, UnpackedArrayFixedSize) {
  auto r = Parse("module t;\n"
                 "  int arr [3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// 18. Integer types with 2D unpacked arrays.
TEST(ParserSection6, Sec6_11_Int2DUnpackedArray) {
  auto r = Parse("module t;\n"
                 "  int matrix[3][4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "matrix");
  ASSERT_GE(item->unpacked_dims.size(), 2u);
}

// Integer type with unpacked dimension using range notation.
TEST(ParserSection6, Sec6_11_IntUnpackedRangeNotation) {
  auto r = Parse("module t;\n"
                 "  int data [0:7];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

static bool ParseOk5(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
// --- Unpacked range dimensions [M:N] ---
TEST(ParserCh5, UnpackedDim_Range) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:0]; endmodule"));
}

TEST(ParserCh5, UnpackedDim_MultiRange) {
  EXPECT_TRUE(ParseOk5("module m; int a[1:2][1:3]; endmodule"));
}

} // namespace
