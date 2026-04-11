#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DeclarationListParsing, MultipleArgsAllWithDefaults) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a = 1, input int b = 2);\n"
      "    compute = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
}

TEST(FunctionDeclParsing, FunctionSingleArgWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x = 5);\n"
      "    return x;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(TaskDeclParsing, TaskSingleArgWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x = 5);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(TaskAndFunctionParsing, MixedDefaultAndNonDefaultArgs) {
  auto r = Parse(
      "module m;\n"
      "  function int fun(int j, string s = \"no\", int k = 0);\n"
      "    return j;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "fun");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 3u);
  EXPECT_EQ(fn->func_args[0].default_value, nullptr);
  EXPECT_NE(fn->func_args[1].default_value, nullptr);
  EXPECT_NE(fn->func_args[2].default_value, nullptr);
}

TEST(TaskAndFunctionParsing, DefaultArgWithExpression) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(int size = 8 * 4);\n"
      "    return size;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "compute");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 1u);
  ASSERT_NE(fn->func_args[0].default_value, nullptr);
  EXPECT_EQ(fn->func_args[0].default_value->kind, ExprKind::kBinary);
}

TEST(TaskAndFunctionParsing, DefaultArgValueOnTask) {
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

TEST(TaskAndFunctionParsing, DefaultArgNoDefault) {
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

TEST(TaskAndFunctionParsing, OutputArgWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  task t1(output logic o = a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* tk = FindFunc(r, "t1");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kOutput);
  ASSERT_NE(tk->func_args[0].default_value, nullptr);
  EXPECT_EQ(tk->func_args[0].default_value->kind, ExprKind::kIdentifier);
}

TEST(TaskAndFunctionParsing, InoutArgWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  logic w;\n"
      "  task t3(inout logic io = w);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* tk = FindFunc(r, "t3");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInout);
  ASSERT_NE(tk->func_args[0].default_value, nullptr);
  EXPECT_EQ(tk->func_args[0].default_value->kind, ExprKind::kIdentifier);
}

TEST(TaskAndFunctionParsing, EmptyPlaceholderArg) {
  auto r = Parse(
      "module m;\n"
      "  task read(int j = 0, int k, int data = 1);\n"
      "  endtask\n"
      "  initial read(, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* call = stmt->expr;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
  ASSERT_EQ(call->args.size(), 2u);
  EXPECT_EQ(call->args[0], nullptr);
  ASSERT_NE(call->args[1], nullptr);
}

}  // namespace
