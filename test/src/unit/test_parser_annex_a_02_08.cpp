#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// §A.2.8 block_item_declaration alternative 1: data_declaration
// data_declaration ::= [ const ] [ var ] [ lifetime ] data_type_or_implicit
//                      list_of_variable_decl_assignments ;

TEST(ParserA28, DataDeclBasicInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "x");
}

TEST(ParserA28, DataDeclConstInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const int x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "x");
}

TEST(ParserA28, DataDeclConstVarInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const var int x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ParserA28, DataDeclAutomaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_is_automatic, true);
}

TEST(ParserA28, DataDeclStaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_is_static, true);
}

TEST(ParserA28, DataDeclMultiVarsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a = 1, b = 2, c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->var_name, "a");
  EXPECT_EQ(body->stmts[1]->var_name, "b");
  EXPECT_EQ(body->stmts[2]->var_name, "c");
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

// data_declaration alternative: type_declaration (typedef)
TEST(ParserA28, TypedefInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    typedef int my_int_t;\n"
              "    my_int_t x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

// data_declaration alternative: package_import_declaration
TEST(ParserA28, ImportInBlock) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  int x = 5;\n"
              "endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import pkg::*;\n"
              "  end\n"
              "endmodule\n"));
}

// §A.2.8 block_item_declaration alternative 2: local_parameter_declaration
TEST(ParserA28, LocalparamInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam int X = 5;\n"
      "    $display(\"%0d\", X);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "X");
}

// §A.2.8 block_item_declaration alternative 3: parameter_declaration
TEST(ParserA28, ParameterInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    parameter int Y = 10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->var_name, "Y");
}

// §A.2.8 block_item_declaration alternative 4: let_declaration
TEST(ParserA28, LetDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let my_add(x, y) = x + y;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, LetDeclNoArgsInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let val = 42;\n"
              "  end\n"
              "endmodule\n"));
}

// attribute_instance prefix on block items
TEST(ParserA28, AttrOnDataDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) int x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, AttrOnLocalparamInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) localparam int X = 5;\n"
              "  end\n"
              "endmodule\n"));
}

// block_item_declaration in fork/join (§9.3.2)
TEST(ParserA28, BlockItemInForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    int x;\n"
      "    x = 5;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  ASSERT_GE(body->fork_stmts.size(), 1u);
  EXPECT_EQ(body->fork_stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ParserA28, BlockItemInForkJoinAny) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_any\n"
              "endmodule\n"));
}

TEST(ParserA28, BlockItemInForkJoinNone) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_none\n"
              "endmodule\n"));
}

// block_item_declaration in function body (§13.4)
TEST(ParserA28, BlockItemInFunction) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x);\n"
      "    int temp;\n"
      "    temp = x + 1;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
}

// block_item_declaration in task body (§13.3)
TEST(ParserA28, BlockItemInTask) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "    int x;\n"
      "    x = 5;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
}

// let_declaration in function body
TEST(ParserA28, LetDeclInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    let inc(x) = x + 1;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// let_declaration in task body
TEST(ParserA28, LetDeclInTask) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task();\n"
              "    let inc(x) = x + 1;\n"
              "  endtask\n"
              "endmodule\n"));
}

// typedef in function body
TEST(ParserA28, TypedefInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    typedef logic [7:0] byte_t;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// import in task body
TEST(ParserA28, ImportInTask) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  int val = 1;\n"
              "endpackage\n"
              "module m;\n"
              "  task my_task();\n"
              "    import pkg::*;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Mixed block items: all 4 alternatives together
TEST(ParserA28, MixedBlockItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    parameter int P = 1;\n"
              "    localparam int LP = 2;\n"
              "    int x = 3;\n"
              "    x = x + P + LP;\n"
              "  end\n"
              "endmodule\n"));
}

// Named block with declarations
TEST(ParserA28, NamedBlockWithDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    parameter int N = 4;\n"
      "    int i;\n"
      "    for (i = 0; i < N; i++) begin\n"
      "    end\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_block");
}

// Nested blocks with declarations
TEST(ParserA28, NestedBlocksWithDecls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    int x = 1;\n"
              "    begin\n"
              "      int y = 2;\n"
              "      x = x + y;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// const with lifetime in block
TEST(ParserA28, ConstWithLifetimeInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    const var automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

// Multiple imports in one statement in block
TEST(ParserA28, ImportMultipleInBlock) {
  EXPECT_TRUE(
      ParseOk("package p1; int a; endpackage\n"
              "package p2; int b; endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import p1::a, p2::b;\n"
              "  end\n"
              "endmodule\n"));
}

// typedef in fork/join
TEST(ParserA28, TypedefInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    typedef int my_t;\n"
              "  join\n"
              "endmodule\n"));
}

// let_declaration in fork/join
TEST(ParserA28, LetDeclInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    let val = 99;\n"
              "  join\n"
              "endmodule\n"));
}

}  // namespace
