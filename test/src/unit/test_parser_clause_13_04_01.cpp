#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(FunctionReturnValueParsing, ReturnTypeInt) {
  auto r = Parse(
      "module m;\n  function int foo(); return 0; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(FunctionReturnValueParsing, ReturnTypeVoid) {
  auto r = Parse("module m;\n  function void bar(); endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(FunctionReturnValueParsing, ReturnTypeLogicPacked) {
  auto r = Parse(
      "module m;\n  function logic [3:0] baz();\n"
      "    return 4'b0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

TEST(FunctionReturnValueParsing, FunctionReturnAndVoidAndDirections) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a, output int b,\n"
      "                       inout int c, ref int d);\n"
      "    b = a;\n"
      "    return a + c + d;\n"
      "  endfunction\n"
      "  function void show(input int val);\n"
      "    $display(\"%d\", val);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl),
      2);
  const auto* compute = FindFunctionByName(r.cu->modules[0]->items, "compute");
  ASSERT_NE(compute, nullptr);
  ASSERT_EQ(compute->func_args.size(), 4u);
  EXPECT_EQ(compute->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(compute->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(compute->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(compute->func_args[3].direction, Direction::kRef);
}

TEST(FunctionReturnValueParsing, ReturnTypeReal) {
  auto r = Parse(
      "module t;\n"
      "  function real compute();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kReal);
}

TEST(FunctionReturnValueParsing, FunctionCallInContAssign) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  assign result = add(x, y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* assign = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(assign, nullptr);
  ASSERT_NE(assign->assign_rhs, nullptr);
  EXPECT_EQ(assign->assign_rhs->kind, ExprKind::kCall);
}

TEST(FunctionReturnValueParsing, NestedFunctionCalls) {
  auto r = Parse(
      "module m;\n"
      "  function int inc(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = inc(inc(a));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);

  ASSERT_EQ(stmt->rhs->args.size(), 1u);
  EXPECT_EQ(stmt->rhs->args[0]->kind, ExprKind::kCall);
}

TEST(FunctionReturnValueParsing, BlockWithReturnInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int compute(input int a, input int b);\n"
              "    begin\n"
              "      int tmp;\n"
              "      tmp = a + b;\n"
              "      return tmp;\n"
              "    end\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(FunctionReturnValueParsing, PackedStructAsFunctionReturn) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } pair_t;\n"
              "  function pair_t make_pair;\n"
              "    input logic [7:0] x, y;\n"
              "    make_pair = {x, y};\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(FunctionReturnValueParsing, ReturnWithComplexExpr) {
  auto r = Parse(
      "module t;\n"
      "  function int compute(int a, int b);\n"
      "    return a * b + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ret = FindReturnStmt(r);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  ASSERT_NE(ret->expr, nullptr);

  EXPECT_EQ(ret->expr->kind, ExprKind::kBinary);
}

TEST(FunctionReturnValueParsing, FunctionCallAsExprInAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial x = func(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->rhs->callee, "func");
  EXPECT_EQ(stmt->rhs->args.size(), 2u);
}

TEST(FunctionReturnValueParsing, FunctionCallAsExpression) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(int a); return a + 1; endfunction\n"
      "  initial x = foo(5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
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

TEST(FunctionReturnValueParsing, FunctionReturnTypeLogicVec) {
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
static ModuleItem* NthItem(ParseResult& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

TEST(FunctionReturnValueParsing, FunctionReturnStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  function point_t make_point;\n"
      "    input int a, b;\n"
      "    make_point = '{a, b};\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 1);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
}
TEST(FunctionReturnValueParsing, VoidFunctionInClass) {
  auto r = Parse(
      "class C;\n"
      "  function void setup();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(FunctionReturnValueParsing, FunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = compute(a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(FunctionReturnValueParsing, SystemCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] val;\n"
      "  initial begin\n"
      "    val = $random;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

TEST(FunctionReturnValueParsing, NonVoidFunctionUsedAsOperand) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int twice(int v); return v * 2; endfunction\n"
              "  logic [31:0] result;\n"
              "  initial result = twice(5);\n"
              "endmodule\n"));
}

TEST(FunctionReturnValueParsing, BareReturnInVoidFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    $display(\"hello\");\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FindFunc(r, "f");
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 2u);
  auto* ret = fn->func_body_stmts[1];
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  EXPECT_EQ(ret->expr, nullptr);
}

TEST(FunctionReturnValueParsing, FunctionNameAssignParsesAsBlockingAssign) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(int a);\n"
      "    foo = a + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  auto* stmt = fn->func_body_stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "foo");
}

TEST(FunctionReturnValueParsing, VoidFunctionCallAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  function void log_it();\n"
      "    $display(\"hi\");\n"
      "  endfunction\n"
      "  initial begin\n"
      "    log_it();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
}

}  // namespace
