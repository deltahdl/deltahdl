// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
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

namespace {

// ---------------------------------------------------------------------------
// task_prototype ::=
//   task [ dynamic_override_specifiers ] task_identifier
//     [ ( [ tf_port_list ] ) ]
// ---------------------------------------------------------------------------
TEST(ParserA27, TaskPrototypeExtern) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "my_task");
}

TEST(ParserA27, TfPortItemVarWithDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "x");
}

// ---------------------------------------------------------------------------
// tf_port_direction: [ const ] ref [ static ]
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortDirectionRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

// ---------------------------------------------------------------------------
// tf_port_item clarification 28: name omitted in prototype
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortItemNoNameInPrototype) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int, output int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
}

// ---------------------------------------------------------------------------
// tf_item_declaration: block_item_declaration and tf_port_declaration mixed
// ---------------------------------------------------------------------------
TEST(ParserA27, TfItemDeclMixed) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    int temp;\n"
      "    temp = a + 1;\n"
      "    b = temp;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
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

// 29. Function with local variables creating subscope
TEST(ParserClause03, Cl3_13_FunctionWithLocalVarsSubscope) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int compute(int a, int b);\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* func = mod->items[0];
  EXPECT_EQ(func->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(func->name, "compute");
  // The function should have body statements (local var + assign + return).
  EXPECT_FALSE(func->func_body_stmts.empty());
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
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(item->func_args[3].direction, Direction::kRef);
}

TEST(ParserA26, FuncBodyNewStyleStickyDirection) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(input int a, int b, int c);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInput);
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
// function_prototype ::=
//   function [ dynamic_override_specifiers ] data_type_or_void
//     function_identifier [ ( [ tf_port_list ] ) ]
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncPrototypeExtern) {
  auto r = Parse(
      "module m;\n"
      "  extern function int foo(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
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

static ModuleItem* FindItemByKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 13.5.3 -- Default argument values
// =============================================================================
TEST(ParserSection13, DefaultArgValues) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a = 0, int b = 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_NE(fn->func_args[0].default_value, nullptr);
  EXPECT_NE(fn->func_args[1].default_value, nullptr);
}

TEST(ParserSection13, DefaultArgValueOnTask) {
  auto r = Parse(
      "module m;\n"
      "  task bar(int x, int y = 10);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "bar");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].default_value, nullptr);
  EXPECT_NE(tk->func_args[1].default_value, nullptr);
}

TEST(ParserSection13, DefaultArgNoDefault) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_EQ(fn->func_args[0].default_value, nullptr);
  EXPECT_EQ(fn->func_args[1].default_value, nullptr);
}

// =============================================================================
// LRM section 13.5.2 -- Const ref arguments
// =============================================================================
TEST(ParserSection13, ConstRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function void bar(const ref int arr);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "bar");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_TRUE(fn->func_args[0].is_const);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
}

TEST(ParserSection13, RefWithoutConst) {
  auto r = Parse(
      "module m;\n"
      "  function void baz(ref int x);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "baz");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_FALSE(fn->func_args[0].is_const);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
}

// =============================================================================
// LRM section 13.5.4 -- Named argument binding
// =============================================================================
TEST(ParserSection13, NamedArgBindingParses) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(.b(2), .a(1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
}

TEST(ParserSection13, NamedArgBindingNames) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(.b(2), .a(1));\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  ASSERT_EQ(call->arg_names.size(), 2u);
  const std::vector<std::string> kExpected = {"b", "a"};
  for (size_t i = 0; i < kExpected.size(); ++i) {
    EXPECT_EQ(call->arg_names[i], kExpected[i]);
  }
}

TEST(ParserSection13, PositionalArgsHaveEmptyNames) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
}

TEST(ParserSection13, PositionalArgsNoNamedArgs) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int a, int b);\n"
      "  endfunction\n"
      "  initial foo(1, 2);\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  // Positional calls: arg_names is empty (no named args detected)
  EXPECT_TRUE(call->arg_names.empty());
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

TEST(ParserSection13, MultipleDimsOnFuncArg) {
  auto r = Parse(
      "module m;\n"
      "  task bar(logic mem[16][8]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "bar");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].unpacked_dims.size(), 2u);
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

TEST(ParserSection13, OldStyleTask) {
  auto r = Parse(
      "module m;\n"
      "  task mytask;\n"
      "    input a;\n"
      "    output b;\n"
      "    b = a;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "mytask");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(tk->func_args[1].direction, Direction::kOutput);
}

// =============================================================================
// LRM section 13.4.1 -- Function return type
// =============================================================================
TEST(ParserSection13, FunctionReturnTypeInt) {
  auto r = Parse(
      "module m;\n"
      "  function int foo();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserSection13, FunctionReturnTypeVoid) {
  auto r = Parse(
      "module m;\n"
      "  function void bar();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "bar");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserSection13, FunctionReturnTypeLogicVec) {
  auto r = Parse(
      "module m;\n"
      "  function logic [7:0] get_byte();\n"
      "    return 8'hAB;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "get_byte");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kLogic);
}

// =============================================================================
// LRM section 13.3.1 -- Static and automatic tasks/functions
// =============================================================================
TEST(ParserSection13, AutomaticFunction) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int fact(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * fact(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "fact");
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  EXPECT_FALSE(fn->is_static);
}

TEST(ParserSection13, StaticTask) {
  auto r = Parse(
      "module m;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "do_stuff");
  ASSERT_NE(tk, nullptr);
  EXPECT_TRUE(tk->is_static);
  EXPECT_FALSE(tk->is_automatic);
}

// =============================================================================
// LRM section 13.6 -- DPI import / export
// =============================================================================
TEST(ParserSection13, DpiImportFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "c_add");
  EXPECT_FALSE(dpi->dpi_is_task);
  EXPECT_FALSE(dpi->dpi_is_pure);
}

TEST(ParserSection13, DpiImportPureFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function int c_mul(int a, int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->dpi_is_pure);
  EXPECT_FALSE(dpi->dpi_is_context);
}

TEST(ParserSection13, DpiImportContextTask) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context task c_display(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->dpi_is_context);
  EXPECT_TRUE(dpi->dpi_is_task);
}

TEST(ParserSection13, DpiImportWithCName) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_real_name = function void sv_wrapper();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->dpi_c_name, "c_real_name");
  EXPECT_EQ(dpi->name, "sv_wrapper");
}

TEST(ParserSection13, DpiExportFunction) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI-C\" function my_sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiExport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "my_sv_func");
}

TEST(ParserSection13, DpiExportTask) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI-C\" task my_sv_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiExport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "my_sv_task");
  EXPECT_TRUE(dpi->dpi_is_task);
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
// =============================================================================
// LRM section 13.8 -- Parameterized tasks and functions
// =============================================================================
TEST(ParserSection13, ParameterizedSubroutine_VirtualClassWithStaticMethod) {
  auto r = Parse(
      "virtual class C#(parameter DECODE_W = 8,\n"
      "                 parameter ENCODE_W = $clog2(DECODE_W));\n"
      "  static function logic [ENCODE_W-1:0] ENCODER_f\n"
      "      (input logic [DECODE_W-1:0] DecodeIn);\n"
      "    ENCODER_f = '0;\n"
      "    for (int i = 0; i < DECODE_W; i++) begin\n"
      "      if (DecodeIn[i]) begin\n"
      "        ENCODER_f = i[ENCODE_W-1:0];\n"
      "        break;\n"
      "      end\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_ClassScopeCall) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] encoder_in;\n"
      "  logic [2:0] encoder_out;\n"
      "  assign encoder_out = C#(8)::ENCODER_f(encoder_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_MultipleStaticMethods) {
  auto r = Parse(
      "virtual class C#(parameter W = 4);\n"
      "  static function logic [W-1:0] encode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  static function logic [W-1:0] decode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_DifferentSpecializations) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [1:0] ra;\n"
      "  logic [2:0] rb;\n"
      "  assign ra = C#(4)::ENCODER_f(a);\n"
      "  assign rb = C#(8)::ENCODER_f(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
TEST(ParserSection13, OldStyleTaskMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  task add;\n"
      "    input a;\n"
      "    input b;\n"
      "    output c;\n"
      "    c = a + b;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "add");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 3u);
  const Direction kExpected[] = {Direction::kInput, Direction::kInput,
                                 Direction::kOutput};
  for (size_t i = 0; i < 3u; ++i) {
    EXPECT_EQ(tk->func_args[i].direction, kExpected[i]);
  }
}

// =============================================================================
// LRM section 13.5.2 -- Const ref arguments (additional tests)
// =============================================================================
TEST(ParserSection13, ConstRefArgOnTask) {
  auto r = Parse(
      "module m;\n"
      "  task process_data(const ref int data[]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "process_data");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_TRUE(tk->func_args[0].is_const);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kRef);
}

TEST(ParserSection13, ConstRefMixedWithOtherDirections) {
  auto r = Parse(
      "module m;\n"
      "  function void compute(input int a, const ref int b, output int c);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "compute");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 3u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kInput);
  EXPECT_FALSE(fn->func_args[0].is_const);
  EXPECT_EQ(fn->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(fn->func_args[1].is_const);
  EXPECT_EQ(fn->func_args[2].direction, Direction::kOutput);
}

TEST(ParserSection13, RefArgOnFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void swap(ref int a, ref int b);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "swap");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
  EXPECT_EQ(fn->func_args[1].direction, Direction::kRef);
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

// Task with end label matching the task name (LRM section 13.3).
TEST(ParserSection13, TaskEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  task do_work(int x);\n"
      "    $display(\"%d\", x);\n"
      "  endtask : do_work\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "do_work");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
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

// =============================================================================
// LRM section 13.3 -- Tasks (additional tests)
// =============================================================================
// Task with timing control in body (tasks may have time-controlling stmts).
TEST(ParserSection13, TaskWithTimingControl) {
  auto r = Parse(
      "module m;\n"
      "  task wait_clk(input int n);\n"
      "    repeat (n) @(posedge clk);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "wait_clk");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInput);
}

}  // namespace
