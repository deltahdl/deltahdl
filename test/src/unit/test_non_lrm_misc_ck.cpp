// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

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
