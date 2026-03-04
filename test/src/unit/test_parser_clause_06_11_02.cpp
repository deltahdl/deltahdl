// §6.11.2: 2-state (two-value) and 4-state (four-value) data types

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// 3. Reg variable declaration produces kVarDecl.
TEST(ParserSection6, Sec6_5_RegVarDeclKind) {
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
TEST(ParserSection6, IntegerTypeShortintDecl) {
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

TEST(ParserSection6, IntegerTypeIntDecl) {
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

TEST(ParserSection6, IntegerTypeLongintDecl) {
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

// --- 4-state integer types ---
TEST(ParserSection6, IntegerTypeIntegerDecl) {
  // 'integer' is 4-state, 32-bit signed (LRM 6.11)
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

TEST(ParserSection6, IntegerTypeLogicDecl) {
  // 'logic' is 4-state, user-defined width, unsigned (LRM 6.11)
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

TEST(ParserSection6, IntegerTypeRegDecl) {
  // 'reg' is identical to 'logic' (LRM 6.11.2)
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

TEST(ParserSection6, IntegerTypeBitDecl) {
  // 'bit' is 2-state, user-defined width, unsigned (LRM 6.11)
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
// 14b. shortint with negative initializer.
TEST(ParserSection6, Sec6_11_ShortintWithNegativeInit) {
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

// 16b. shortint as function return type.
TEST(ParserSection6, Sec6_11_ShortintFunctionReturnType) {
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

TEST(ParserSection6, All2StateTypes) {
  // Verify all 2-state types parse correctly together
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte b;\n"
              "  shortint si;\n"
              "  int i;\n"
              "  longint li;\n"
              "  bit bv;\n"
              "endmodule\n"));
}

TEST(ParserSection6, All4StateTypes) {
  // Verify all 4-state types parse correctly together
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic l;\n"
              "  reg r;\n"
              "  integer ig;\n"
              "  time t;\n"
              "endmodule\n"));
}
// =============================================================================
// Section 8.2 -- Data type syntax
// =============================================================================
// Integer vector types with packed dimensions.
TEST(ParserSection8, DataTypeSyntaxIntegerVector) {
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

// Integer atom types.
TEST(ParserSection8, DataTypeSyntaxIntegerAtom) {
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

// 30. Reg used in always block (procedural context).
TEST(ParserSection6, Sec6_5_RegInAlwaysBlock) {
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

// =============================================================================
// LRM section 6.11.2 -- reg and logic equivalence
// =============================================================================
// 22. reg and logic both parse to their respective DataTypeKind.
TEST(ParserSection6, Sec6_11_2_RegAndLogicDistinctKinds) {
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

// =============================================================================
// LRM section 6.11 -- Integer types in package scope
// =============================================================================
// 26. Integer types in package scope.
TEST(ParserSection6, Sec6_11_IntegerTypesInPackage) {
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

// =============================================================================
// LRM section 6.11 -- Integer types in class members
// =============================================================================
// 27. Integer types in class members.
TEST(ParserSection6, Sec6_11_IntegerTypesInClassMembers) {
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

// Integer (4-state) with initializer.
TEST(ParserSection6, Sec6_11_IntegerWithInit) {
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

// Longint function return type.
TEST(ParserSection6, Sec6_11_LongintFunctionReturnType) {
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

// Integer function return type.
TEST(ParserSection6, Sec6_11_IntegerFunctionReturnType) {
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

// Multiple integer types as function parameters with directions.
TEST(ParserSection6, Sec6_11_MixedIntegerFuncParams) {
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

// time type with unpacked dimensions.
TEST(ParserSection6, Sec6_11_TimeUnpackedArray) {
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

// =========================================================================
// §6.3: Value set — 4-state vs 2-state type queries
// =========================================================================
TEST(ParserSection6, ValueSet_IntegerIs4State) {
  // §6.3: integer is a 4-state type.
  EXPECT_TRUE(Is4stateType(DataTypeKind::kInteger));
}

TEST(ParserSection6, ValueSet_IntIs2State) {
  // §6.3: int is a 2-state type.
  EXPECT_FALSE(Is4stateType(DataTypeKind::kInt));
}
TEST(ParserSection6, ByteVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
}

TEST(ParserSection6, LongintVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  longint li;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
}

// =============================================================================
// LRM section 6.11 -- Integer data types
// =============================================================================
// --- 2-state integer types ---
TEST(ParserSection6, IntegerTypeByteDecl) {
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

}  // namespace
