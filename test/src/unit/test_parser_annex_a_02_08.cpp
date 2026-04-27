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

// Lifetime-keyword tests on block-scoped variable declarations are §6.21
// rules; the corresponding parser tests live in test_parser_clause_06_21.cpp
// (e.g. AutomaticVarDeclInBlock, StaticVarInBeginEnd).

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

// --- {attribute_instance} prefix ---

TEST(BlockItemDeclParsing, DataDeclWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis *) int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_FALSE(stmt->attrs.empty());
}

TEST(BlockItemDeclParsing, LocalparamWithAttribute) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    (* mark *) localparam int W = 8;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(BlockItemDeclParsing, ParameterWithAttribute) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    (* mark *) parameter int D = 4;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(BlockItemDeclParsing, LetDeclWithAttribute) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    (* mark *) let double(x) = x * 2;\n"
      "  end\n"
      "endmodule\n"));
}

// --- additional contexts ---

TEST(BlockItemDeclParsing, FunctionBodyBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  function int f(int a);\n"
      "    int temp;\n"
      "    temp = a + 1;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFunctionDecl(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_GE(fn->func_body_stmts.size(), 1u);
  EXPECT_EQ(fn->func_body_stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockItemDeclParsing, AlwaysCombBlockItem) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  always_comb begin\n"
      "    int temp;\n"
      "    temp = 0;\n"
      "  end\n"
      "endmodule\n"));
}

// --- mixed alternatives ---

TEST(BlockItemDeclParsing, MixedAlternativesInOneBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam int W = 8;\n"
      "    parameter int D = 4;\n"
      "    int x;\n"
      "    let inc(a) = a + 1;\n"
      "    x = inc(W);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_GE(stmts.size(), 5u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kBlockItemDecl);
}

// --- data_declaration with var prefix ---

TEST(BlockItemDeclParsing, DataDeclWithVarPrefix) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    var int x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "x");
}

// --- data_declaration: import wildcard ---

TEST(BlockItemDeclParsing, ImportWildcardInBlock) {
  EXPECT_TRUE(ParseOk(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin\n"
      "    import pkg::*;\n"
      "  end\n"
      "endmodule\n"));
}

// --- let_declaration without arguments ---

TEST(BlockItemDeclParsing, LetDeclNoArgsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    let ZERO = 0;\n"
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

}  // namespace
