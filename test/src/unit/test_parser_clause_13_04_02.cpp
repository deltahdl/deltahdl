// §13.4.2: Static and automatic functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2FunctionDeclAutomaticParse) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
}

TEST(ParserAnnexA, A2FunctionDeclAutomaticProps) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->func_args.size(), 2u);
}

TEST(ParserA213, LifetimeInFunction) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int calc; return 0; endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
}

// ---------------------------------------------------------------------------
// function_declaration ::=
//   function [ dynamic_override_specifiers ] [ lifetime ]
//     function_body_declaration
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n  function automatic int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA26, FuncLifetimeStatic) {
  auto r = Parse(
      "module m;\n  function static int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA26, FuncLifetimeDefault) {
  auto r = Parse(
      "module m;\n  function int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

struct ParseResult4e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4e Parse(const std::string& src) {
  ParseResult4e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// 18. Recursive automatic function with base case (Fibonacci)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_RecursiveAutoFuncFibonacci) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int fibonacci(int n);\n"
      "    if (n == 0)\n"
      "      return 0;\n"
      "    else if (n == 1)\n"
      "      return 1;\n"
      "    else\n"
      "      return fibonacci(n - 1) + fibonacci(n - 2);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->name, "fibonacci");
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kIf);
  EXPECT_NE(item->func_body_stmts[0]->else_branch, nullptr);
}

// =============================================================================
// 20. Automatic function in class context
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  function automatic int get_id();\n"
              "    return 42;\n"
              "  endfunction\n"
              "endclass\n"));
}

}  // namespace
