#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BlockItemDeclParsing, BlockItemDataDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "x");
}

TEST(BlockItemDeclParsing, BlockItemDataDeclWithInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_NE(stmt->var_init, nullptr);
}

TEST(BlockItemDeclParsing, BlockItemLocalparamDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam int WIDTH = 8;\n"
      "    $display(\"%0d\", WIDTH);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "WIDTH");
}

TEST(BlockItemDeclParsing, BlockItemParameterDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter int DEPTH = 4;\n"
      "    $display(\"%0d\", DEPTH);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
}

TEST(BlockItemDeclParsing, BlockItemLetDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    let add(a, b) = a + b;\n"
      "    $display(\"%0d\", add(1, 2));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockItemDecl);
  ASSERT_NE(stmt->decl_item, nullptr);
  EXPECT_EQ(stmt->decl_item->kind, ModuleItemKind::kLetDecl);
}

TEST(BlockItemDeclParsing, BlockItemTypedefDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    typedef int my_int;\n"
      "    my_int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockItemDecl);
  ASSERT_NE(stmt->decl_item, nullptr);
  EXPECT_EQ(stmt->decl_item->kind, ModuleItemKind::kTypedef);
}

TEST(BlockItemDeclParsing, BlockItemImportDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int my_type;\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin\n"
      "    import pkg::my_type;\n"
      "    my_type x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockItemDecl);
  ASSERT_NE(stmt->decl_item, nullptr);
  EXPECT_EQ(stmt->decl_item->kind, ModuleItemKind::kImportDecl);
}

TEST(BlockItemDeclParsing, BlockItemConstDataDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const int C = 99;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_const);
}

TEST(BlockItemDeclParsing, BlockItemAutomaticLifetime) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x = 0;\n"
      "    x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
}

TEST(BlockItemDeclParsing, BlockItemStaticLifetime) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_static);
}

TEST(BlockItemDeclParsing, TaskBodyBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    int local_var;\n"
      "    local_var = 42;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(BlockItemDeclParsing, ForkJoinBlockItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    begin x = 1; end\n"
              "  join\n"
              "endmodule\n"));
}

TEST(BlockItemDeclParsing, MultipleBlockItemDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a;\n"
      "    int b;\n"
      "    int c;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_GE(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kVarDecl);
}

}  // namespace
