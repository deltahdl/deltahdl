#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* mark *) localparam int W = 8;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BlockItemDeclParsing, ParameterWithAttribute) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* mark *) parameter int D = 4;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BlockItemDeclParsing, LetDeclWithAttribute) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* mark *) let double(x) = x * 2;\n"
              "  end\n"
              "endmodule\n"));
}

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
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always_comb begin\n"
              "    int temp;\n"
              "    temp = 0;\n"
              "  end\n"
              "endmodule\n"));
}

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

TEST(BlockItemDeclParsing, MultipleAttributeInstancesOnDataDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* a *) (* b *) int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_GE(stmt->attrs.size(), 2u);
}

TEST(BlockItemDeclParsing, ErrorBlockItemLocalparamMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam int W = 8\n"
      "    $display(\"%0d\", W);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got system identifier", 4,
                            "6.20.1"));
}

TEST(BlockItemDeclParsing, ErrorBlockItemParameterMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter int D = 4\n"
      "    $display(\"%0d\", D);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got system identifier", 4,
                            "6.20.1"));
}

TEST(BlockItemDeclParsing, ErrorNetDeclNotABlockItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wire w;\n"
      "    w = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(BlockItemDeclParsing, InlineEnumVariableInATaskBody) {
  auto r = Parse(
      "module m;\n"
      "  task tk;\n"
      "    enum {p, q} z;\n"
      "    z = q;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* tk = r.cu->modules[0]->items[0];
  ASSERT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(tk->func_body_stmts.size(), 2u);
  auto* z = tk->func_body_stmts[0];
  EXPECT_EQ(z->kind, StmtKind::kVarDecl);
  EXPECT_EQ(z->var_name, "z");
  EXPECT_EQ(z->var_decl_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(z->var_decl_type.enum_members.size(), 2u);
  EXPECT_EQ(z->var_decl_type.enum_members[1].name, "q");
}

TEST(BlockItemDeclParsing, InlineAggregateVariablesInAnInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    struct {int x; byte y;} a, b;\n"
      "    union packed {bit [15:0] w; bit [1:0][7:0] h;} u;\n"
      "    enum {r, s} e = s;\n"
      "    a.x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& body = r.cu->modules[0]->items[0]->body->stmts;
  ASSERT_EQ(body.size(), 5u);
  EXPECT_EQ(body[0]->var_name, "a");
  EXPECT_EQ(body[0]->var_decl_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(body[1]->var_name, "b");
  EXPECT_EQ(body[1]->var_decl_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(body[2]->var_name, "u");
  EXPECT_EQ(body[2]->var_decl_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(body[2]->var_decl_type.is_packed);
  EXPECT_EQ(body[3]->var_name, "e");
  EXPECT_EQ(body[3]->var_decl_type.kind, DataTypeKind::kEnum);
  EXPECT_NE(body[3]->var_init, nullptr);
  for (int i = 0; i < 4; ++i) EXPECT_EQ(body[i]->kind, StmtKind::kVarDecl);
  EXPECT_NE(body[4]->kind, StmtKind::kVarDecl);
}

TEST(BlockItemDeclParsing, NettypeDeclIsABlockItem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    nettype logic [3:0] nt;\n"
      "    $display(\"x\");\n"
      "  end\n"
      "  task t;\n"
      "    nettype real rt;\n"
      "  endtask\n"
      "  function int f;\n"
      "    nettype bit nb;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto declares_nettype = [](const Stmt* s, std::string_view name) {
    return s->kind == StmtKind::kBlockItemDecl &&
           s->decl_item->kind == ModuleItemKind::kNettypeDecl &&
           s->decl_item->name == name;
  };
  EXPECT_TRUE(declares_nettype(FirstInitialStmt(r), "nt"));
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3U);
  EXPECT_TRUE(declares_nettype(items[1]->func_body_stmts[0], "rt"));
  EXPECT_TRUE(declares_nettype(items[2]->func_body_stmts[0], "nb"));
}

}  // namespace
