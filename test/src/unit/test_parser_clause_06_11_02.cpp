#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(TwoStateAndFourState, RegVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_net);
}
TEST(TwoStateAndFourState, IntegerTypeShortintDecl) {
  auto r = Parse(
      "module m;\n"
      "  shortint si;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(item->name, "si");
}

TEST(TwoStateAndFourState, IntegerTypeIntDecl) {
  auto r = Parse(
      "module m;\n"
      "  int i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "i");
}

TEST(TwoStateAndFourState, IntegerTypeLongintDecl) {
  auto r = Parse(
      "module m;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->name, "li");
}

TEST(TwoStateAndFourState, IntegerTypeIntegerDecl) {
  auto r = Parse(
      "module m;\n"
      "  integer x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(item->name, "x");
}

TEST(TwoStateAndFourState, IntegerTypeLogicDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(TwoStateAndFourState, IntegerTypeRegDecl) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->name, "r");
}

TEST(TwoStateAndFourState, IntegerTypeBitDecl) {
  auto r = Parse(
      "module m;\n"
      "  bit [31:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->name, "val");
}

TEST(TwoStateAndFourState, ShortintWithNegativeInit) {
  auto r = Parse(
      "module t;\n"
      "  shortint s = -1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(TwoStateAndFourState, ShortintFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function shortint get_short();\n"
      "    return 16'd100;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kShortint);
}

TEST(TwoStateAndFourState, All2StateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte b;\n"
              "  shortint si;\n"
              "  int i;\n"
              "  longint li;\n"
              "  bit bv;\n"
              "endmodule\n"));
}

TEST(TwoStateAndFourState, All4StateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic l;\n"
              "  reg r;\n"
              "  integer ig;\n"
              "  time t;\n"
              "endmodule\n"));
}

TEST(TwoStateAndFourState, DataTypeSyntaxIntegerVector) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  bit [15:0] addr;\n"
      "  reg [3:0] nibble;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->name, "data");
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(items[1]->name, "addr");
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(items[2]->name, "nibble");
}

TEST(TwoStateAndFourState, DataTypeSyntaxIntegerAtom) {
  auto r = Parse(
      "module m;\n"
      "  byte b;\n"
      "  shortint si;\n"
      "  int i;\n"
      "  longint li;\n"
      "  integer ig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 5u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kInteger);
}

TEST(TwoStateAndFourState, RegInAlwaysBlock) {
  auto r = Parse(
      "module t;\n"
      "  reg clk;\n"
      "  always #5 clk = ~clk;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(items[1]->body, nullptr);
}

TEST(TwoStateAndFourState, RegAndLogicDistinctKinds) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "  logic l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(items[0]->name, "r");
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[1]->name, "l");
}

TEST(TwoStateAndFourState, IntegerTypesInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  int pkg_count;\n"
      "  byte pkg_flags;\n"
      "  longint pkg_id;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto& items = r.cu->packages[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[0]->name, "pkg_count");
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[1]->name, "pkg_flags");
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(items[2]->name, "pkg_id");
}

TEST(TwoStateAndFourState, IntegerTypesInClassMembers) {
  auto r = Parse(
      "class Counter;\n"
      "  int value;\n"
      "  byte status;\n"
      "  longint timestamp;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 3u);
  EXPECT_EQ(members[0]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(members[0]->name, "value");
  EXPECT_EQ(members[1]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(members[1]->name, "status");
  EXPECT_EQ(members[2]->data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(members[2]->name, "timestamp");
}

TEST(TwoStateAndFourState, IntegerWithInit) {
  auto r = Parse(
      "module t;\n"
      "  integer idx = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(TwoStateAndFourState, LongintFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function longint get_id();\n"
      "    return 64'd1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLongint);
}

TEST(TwoStateAndFourState, IntegerFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function integer get_count();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInteger);
}

TEST(TwoStateAndFourState, MixedIntegerFuncParams) {
  auto r = Parse(
      "module t;\n"
      "  function void process(input byte cmd, input int data,\n"
      "                        output longint result);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[2].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->func_args[2].direction, Direction::kOutput);
}

TEST(TwoStateAndFourState, TimeUnpackedArray) {
  auto r = Parse(
      "module t;\n"
      "  time timestamps[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(item->name, "timestamps");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(TwoStateAndFourState, IntegerIsFourState) {
  EXPECT_TRUE(Is4stateType(DataTypeKind::kInteger));
}

TEST(TwoStateAndFourState, IntIsTwoState) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kInt));
}
TEST(TwoStateAndFourState, ByteVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
}

TEST(TwoStateAndFourState, LongintVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
}

TEST(TwoStateAndFourState, IntegerTypeByteDecl) {
  auto r = Parse(
      "module m;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->name, "b");
}

TEST(TwoStateAndFourState, LogicVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "data");
}

TEST(TwoStateAndFourState, RegWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  reg [15:0] wide_reg;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
  EXPECT_EQ(item->name, "wide_reg");
}

}  // namespace
