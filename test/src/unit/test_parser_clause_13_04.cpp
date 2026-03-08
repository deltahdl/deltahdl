#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(ParserSection4, Sec4_9_3_AutoFuncWithOutputArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void compute(input int a, output int b);\n"
      "    b = a * 3;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserSection13, FunctionDefaultDirectionInput) {
  auto r = Parse(
      "module m;\n"
      "  function int f(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = r.cu->modules[0]->items[0];
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(fn->func_args[1].direction, Direction::kInput);
}

TEST(ParserSection13, FunctionDirectionStickyOutput) {
  auto r = Parse(
      "module m;\n"
      "  function void f(output int a, int b);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = r.cu->modules[0]->items[0];
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kOutput);
  EXPECT_EQ(fn->func_args[1].direction, Direction::kOutput);
}

TEST(ParserSection13, FunctionMultipleStmtsSequential) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    int x;\n"
      "    x = 1;\n"
      "    x = x + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FindFunc(r, "f");
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 3u);
}

TEST(ParserSection13, FunctionRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function void f(ref int a);\n"
      "    a = a + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FindFunc(r, "f");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
}

}
