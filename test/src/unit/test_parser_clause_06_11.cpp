// §6.11: Integer data types

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection6, IntegerTypeTimeDecl) {
  // 'time' is 4-state, 64-bit unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  time t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(item->name, "t");
}
// 16. Integer types as function return types.
TEST(ParserSection6, Sec6_11_ByteFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function byte get_byte();\n"
      "    return 8'hAB;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kByte);
}

// 17. Integer types in task ports.
TEST(ParserSection6, Sec6_11_IntegerTypesInTaskPorts) {
  auto r = Parse(
      "module t;\n"
      "  task t1(input int x, output longint y);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

// =============================================================================
// LRM section 6.11 -- Additional coverage for integer types
// =============================================================================
// Longint with initializer.
TEST(ParserSection6, Sec6_11_LongintWithInit) {
  auto r = Parse(
      "module t;\n"
      "  longint big = 64'hDEAD_BEEF_CAFE_BABE;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  ASSERT_NE(item->init_expr, nullptr);
}
TEST(ParserSection6, IntVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "count");
}

// --- interface_class_type ---
// ps_class_identifier [parameter_value_assignment]
// (grammatically same as single class_type)
// --- integer_type ---
// integer_vector_type | integer_atom_type
// --- integer_atom_type ---
// byte | shortint | int | longint | integer | time
TEST(ParserA221, IntegerAtomTypes) {
  auto r = Parse(
      "module m;\n"
      "  byte a;\n"
      "  shortint b;\n"
      "  int c;\n"
      "  longint d;\n"
      "  integer e;\n"
      "  time f;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind,
            DataTypeKind::kShortint);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(r.cu->modules[0]->items[3]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(r.cu->modules[0]->items[4]->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(r.cu->modules[0]->items[5]->data_type.kind, DataTypeKind::kTime);
}

}  // namespace
