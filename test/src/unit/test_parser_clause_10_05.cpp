#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA24, VarDeclAssignmentWithInit) {
  auto r = Parse("module m; int x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}
TEST(ParserSection6, VariableInitialization) {
  auto r = Parse(
      "module t;\n"
      "  logic v = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection4, Sec4_6_VarInitAtDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_NE(item->init_expr, nullptr);
}
TEST(ParserCh90301, BlockVarDecl_WithInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_NE(blk->stmts[0]->var_init, nullptr);
}

TEST(ParserSection10, Sec10_5_VarInitWithExpr) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] consta = 8'hF0;\n"
      "  logic [7:0] constb = 8'h0F;\n"
      "  logic [7:0] v = consta & constb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  auto* v = items[2];
  EXPECT_EQ(v->name, "v");
  ASSERT_NE(v->init_expr, nullptr);
  EXPECT_EQ(v->init_expr->kind, ExprKind::kBinary);
}

TEST(ParserSection10, Sec10_5_MixedInitInOneStmt) {
  auto r = Parse(
      "module m;\n"
      "  int a = 1, b, c = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_NE(items[0]->init_expr, nullptr);
  EXPECT_EQ(items[1]->init_expr, nullptr);
  EXPECT_NE(items[2]->init_expr, nullptr);
}

TEST(ParserSection10, Sec10_5_BlockLocalWithExprInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 2 + 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_NE(blk->stmts[0]->var_init, nullptr);
}

}  // namespace
