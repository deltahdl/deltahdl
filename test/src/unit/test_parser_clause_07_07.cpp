#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, TaskWithArrayArg) {
  auto r = Parse(
      "module m;\n"
      "  task fun(int a[3:1][3:1]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->name, "fun");
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_GE(item->func_args[0].unpacked_dims.size(), 2u);
}

TEST(AggregateTypeParsing, FuncWithDynamicArrayArg) {
  auto r = Parse(
      "module m;\n"
      "  function int sum(int arr[]);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  ASSERT_EQ(item->func_args[0].unpacked_dims.size(), 1u);

  EXPECT_EQ(item->func_args[0].unpacked_dims[0], nullptr);
}

TEST(AggregateTypeParsing, TaskWithMultipleArrayArgs) {
  auto r = Parse(
      "module m;\n"
      "  task t(input int a[4], output int b[8]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_FALSE(item->func_args[0].unpacked_dims.empty());
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_FALSE(item->func_args[1].unpacked_dims.empty());
}

TEST(AggregateTypeParsing, FuncWithStringArrayArg) {
  auto r = Parse(
      "module m;\n"
      "  task t(string arr[4:1]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kString);
  EXPECT_FALSE(item->func_args[0].unpacked_dims.empty());
}

TEST(AggregateTypeParsing, FixedSizeArrayArg) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int data[3]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims.size(), 1u);
}

TEST(AggregateTypeParsing, FuncWithAssocArrayArg) {
  auto r = Parse(
      "module t;\n"
      "  function void foo(int aa[string]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, TaskWithAssocArrayInOut) {
  auto r = Parse(
      "module t;\n"
      "  task bar(input int a[int], output int b[int]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
