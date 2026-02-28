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

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// 28. Function without explicit lifetime (default — static in module)
// =============================================================================
TEST(ParserSection4, Sec4_9_4_FuncNoExplicitLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FirstFuncOrTask(r);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  // No explicit lifetime — both flags should be false.
  EXPECT_FALSE(fn->is_static);
  EXPECT_FALSE(fn->is_automatic);
  EXPECT_EQ(fn->name, "adder");
}

// =============================================================================
// 22. Mixed static and automatic functions in same module
// =============================================================================
TEST(ParserSection4, Sec4_9_3_MixedStaticAutoFuncsInModule) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int auto_fn(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  function static int static_fn(int x);\n"
      "    return x - 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* auto_fn = r.cu->modules[0]->items[0];
  auto* static_fn = r.cu->modules[0]->items[1];
  EXPECT_TRUE(auto_fn->is_automatic);
  EXPECT_FALSE(auto_fn->is_static);
  EXPECT_TRUE(static_fn->is_static);
  EXPECT_FALSE(static_fn->is_automatic);
}

// =============================================================================
// 25. Function without explicit lifetime (implicit static in module)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_FuncNoLifetimeQualifier) {
  auto r = Parse(
      "module m;\n"
      "  function int plain_fn(int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

// =============================================================================
// 28. Automatic function returning logic with packed dimensions
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncReturningLogic) {
  auto r = Parse(
      "module m;\n"
      "  function automatic logic [7:0] get_byte(int idx);\n"
      "    return idx;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

}  // namespace
