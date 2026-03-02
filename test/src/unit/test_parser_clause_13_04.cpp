// §13.4: Functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// function_body_declaration (old-style ports)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  function int foo;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    foo = a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

// --- Test helpers ---
struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult14 Parse(const std::string& src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// LRM section 13.4 -- Functions (additional tests)
// =============================================================================
// Function with no ports (implicit return by function name assignment).
TEST(ParserSection13, FunctionNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  function int get_magic();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "get_magic");
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->func_args.empty());
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
}

// Function with multiple statements in body.
TEST(ParserSection13, FunctionMultipleBodyStmts) {
  auto r = Parse(
      "module m;\n"
      "  function int clamp(int val, int lo, int hi);\n"
      "    if (val < lo) return lo;\n"
      "    if (val > hi) return hi;\n"
      "    return val;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "clamp");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 3u);
  EXPECT_GE(fn->func_body_stmts.size(), 3u);
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
// 23. Automatic function with input/output/inout ports
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncWithAllPortDirs) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void multi_dir(\n"
      "      input int a,\n"
      "      output int b,\n"
      "      inout int c);\n"
      "    b = a + c;\n"
      "    c = a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(item->func_args[2].data_type.kind, DataTypeKind::kInt);
}

TEST(Parser, FunctionDecl) {
  auto r = Parse(
      "module t;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
  std::string expected[] = {"a", "b"};
  ASSERT_EQ(item->func_args.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(item->func_args[i].name, expected[i]) << "arg " << i;
  }
}

TEST(ParserA23, ListOfTfVariableIdentifiersThree) {
  auto r = Parse(
      "module m;\n"
      "  function int sum3;\n"
      "    input int x, y, z;\n"
      "    sum3 = x + y + z;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[1].name, "y");
  EXPECT_EQ(item->func_args[2].name, "z");
}

TEST(ParserA26, FuncReturnTypeImplicit) {
  auto r =
      Parse("module m;\n  function foo(); return 1; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kImplicit);
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

// 15. Integer types as function parameters.
TEST(ParserSection6, Sec6_11_IntegerTypesAsFunctionParams) {
  auto r = Parse(
      "module t;\n"
      "  function void f(int a, byte b);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA26, FuncReturnTypeImplicitSigned) {
  auto r = Parse(
      "module m;\n  function signed [7:0] foo();\n"
      "    return 0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->return_type.is_signed);
}

TEST(ParserA26, FuncBodyNewStyleWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA26, FuncBodyNewStyleMultipleDirections) {
  auto r = Parse(
      "module m;\n"
      "  function void xfer(input int a, output int b, inout int c, ref int "
      "d);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyFuncArgDirections(r.cu->modules[0]->items[0],
                          {Direction::kInput, Direction::kOutput,
                           Direction::kInout, Direction::kRef});
}

// ---------------------------------------------------------------------------
// function_statement ::= statement
// function_statement_or_null ::= function_statement | { attribute_instance } ;
// ---------------------------------------------------------------------------
// §13: function_statement — regular statement in function body
TEST(ParserA604, FunctionStatement) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    a = 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kBlockingAssign);
}

// §13: multiple function statements including null
TEST(ParserA604, FunctionBodyMultipleStatements) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    a = 1;\n"
      "    ;\n"
      "    b = 2;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 3u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(func->func_body_stmts[1]->kind, StmtKind::kNull);
  EXPECT_EQ(func->func_body_stmts[2]->kind, StmtKind::kBlockingAssign);
}

using CheckerParseTest = ProgramTestParse;

// --- Block-level var decl in function body ---
TEST(ParserSection18, FuncBodyVarDecl) {
  auto r = Parse(
      "module top;\n"
      "  function int foo();\n"
      "    int x;\n"
      "    x = 5;\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// ---------------------------------------------------------------------------
// function_body_declaration (new-style ports)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyNewStyleEmptyPorts) {
  auto r =
      Parse("module m;\n  function void foo();\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(ParserA26, FuncBodyNewStyleStickyDirection) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(input int a, int b, int c);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyFuncArgDirections(
      r.cu->modules[0]->items[0],
      {Direction::kInput, Direction::kInput, Direction::kInput});
}

TEST(ParserA26, FuncBodyWithBlockItemDecl) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x);\n"
      "    int temp;\n"
      "    temp = x + 1;\n"
      "    return temp;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(ParserA26, FuncBodyWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  function void foo();\n"
      "  endfunction : foo\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "foo");
}

TEST(ParserA26, FuncBodyOldStyleOutputPort) {
  auto r = Parse(
      "module m;\n"
      "  function void xfer;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    b = a;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

// ---------------------------------------------------------------------------
// function_body_declaration: argument unpacked dimensions (§13.4)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncArgUnpackedDim) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(input int arr [4]);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims.size(), 1u);
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

static ModuleItem* FindFunc(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl) {
      continue;
    }
    if (item->name == name) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 13.4 -- Array parameters on function args
// =============================================================================
TEST(ParserSection13, ArrayParamOnFuncArg) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int data[3]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_EQ(fn->func_args[0].unpacked_dims.size(), 1u);
}

TEST(ParserSection13, NoDimsOnFuncArg) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int x);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_TRUE(fn->func_args[0].unpacked_dims.empty());
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
TEST(ParserSection13, OldStyleFunction) {
  auto r = Parse(
      "module m;\n"
      "  function [7:0] myfunc;\n"
      "    input [7:0] a;\n"
      "    myfunc = a + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "myfunc");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kInput);
}

// =============================================================================
// LRM section 13.1 -- Tasks and functions overview (additional tests)
// =============================================================================
// Function with end label matching the function name (LRM section 13.4).
TEST(ParserSection13, FunctionEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction : add\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "add");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
}

// Function with empty body.
TEST(ParserSection13, FunctionEmptyBody) {
  auto r = Parse(
      "module m;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "nop");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kVoid);
  EXPECT_TRUE(fn->func_body_stmts.empty());
}

}  // namespace
