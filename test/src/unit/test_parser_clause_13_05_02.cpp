#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA26, FuncBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(const ref int x);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TaskBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDirectionConstRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDeclOldStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    const ref int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserSection4, Sec4_9_3_AutoFuncWithRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void swap(ref int x, ref int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[1].direction, Direction::kRef);
  EXPECT_EQ(item->func_args[1].name, "y");
}

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

TEST(ParserSection13, AutomaticFunctionWithRef) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int crc(ref byte packet[]);\n"
      "    crc = 0;\n"
      "    for (int j = 0; j < 10; j++) begin\n"
      "      crc ^= packet[j];\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "crc");
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  ASSERT_EQ(fn->func_args.size(), 1u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
}

TEST(ParserSection4, Sec4_9_3_AutoFuncWithConstRefArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int read_only(const ref int data);\n"
      "    return data;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].name, "data");
}

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

}  // namespace
