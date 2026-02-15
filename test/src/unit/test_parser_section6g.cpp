#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6g Parse(const std::string& src) {
  ParseResult6g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FirstItem(ParseResult6g& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// =============================================================================
// LRM section 6.11 -- Integer data types: packed dimensions
// =============================================================================

// 1. Packed dimensions on logic type.
TEST(ParserSection6, Sec6_11_LogicPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
  EXPECT_EQ(item->name, "data");
}

// 1b. Packed dimensions on bit type.
TEST(ParserSection6, Sec6_11_BitPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  bit [31:0] word;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// 1c. Packed dimensions on reg type.
TEST(ParserSection6, Sec6_11_RegPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  reg [3:0] nibble;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// 2. Multiple packed dimensions on logic type.
TEST(ParserSection6, Sec6_11_MultiplePackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0][7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  EXPECT_FALSE(item->data_type.extra_packed_dims.empty());
}

// 3. Unpacked dimensions on int type (fixed-size array).
TEST(ParserSection6, Sec6_11_IntUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  int arr[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// 3b. Unpacked dimensions on logic with packed dims (memory array).
TEST(ParserSection6, Sec6_11_LogicPackedAndUnpackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem[256];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// 4. Combined packed + unpacked dims with range notation.
TEST(ParserSection6, Sec6_11_PackedAndUnpackedWithRange) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_FALSE(item->unpacked_dims.empty());
  EXPECT_EQ(item->name, "mem");
}

// 5. Signed with packed dims: logic signed [15:0].
TEST(ParserSection6, Sec6_11_LogicSignedWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic signed [15:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// 5b. Unsigned with packed dims: bit unsigned [7:0].
TEST(ParserSection6, Sec6_11_BitUnsignedWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  bit unsigned [7:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

// 6. byte signed explicitly (redundant but valid).
TEST(ParserSection6, Sec6_11_ByteSignedExplicit) {
  auto r = Parse(
      "module t;\n"
      "  byte signed bs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "bs");
}

// 7. byte unsigned override.
TEST(ParserSection6, Sec6_11_ByteUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  byte unsigned bu;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "bu");
}

// 8. shortint unsigned override.
TEST(ParserSection6, Sec6_11_ShortintUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  shortint unsigned su;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "su");
}

// 9. longint unsigned override.
TEST(ParserSection6, Sec6_11_LongintUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  longint unsigned lu;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "lu");
}

// 10. integer unsigned override.
TEST(ParserSection6, Sec6_11_IntegerUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  integer unsigned iu;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "iu");
}

// 11. time signed override.
TEST(ParserSection6, Sec6_11_TimeSignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  time signed ts;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ts");
}

// 12. bit signed override.
TEST(ParserSection6, Sec6_11_BitSignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  bit signed bs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "bs");
}

// 13. Multiple variables with packed dims share the same type.
TEST(ParserSection6, Sec6_11_MultipleVarsWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->name, "c");
  for (auto* item : items) {
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
    ASSERT_NE(item->data_type.packed_dim_left, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  }
}

// 14. Integer types with initializer expressions.
TEST(ParserSection6, Sec6_11_ByteWithInitializer) {
  auto r = Parse(
      "module t;\n"
      "  byte b = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->name, "b");
  ASSERT_NE(item->init_expr, nullptr);
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

// 15. Integer types as function parameters.
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

// 18. Integer types with 2D unpacked arrays.
TEST(ParserSection6, Sec6_11_Int2DUnpackedArray) {
  auto r = Parse(
      "module t;\n"
      "  int matrix[3][4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "matrix");
  ASSERT_GE(item->unpacked_dims.size(), 2u);
}

// 19. Integer var with complex initializer expression.
TEST(ParserSection6, Sec6_11_IntWithComplexInit) {
  auto r = Parse(
      "module t;\n"
      "  int x = 1 + 2 * 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "x");
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kBinary);
}

// 20. Static lifetime qualifier with integer type.
TEST(ParserSection6, Sec6_11_StaticLifetimeInt) {
  auto r = Parse(
      "module t;\n"
      "  function automatic int count();\n"
      "    static int counter = 0;\n"
      "    counter = counter + 1;\n"
      "    return counter;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 21. Automatic lifetime qualifier with integer type.
TEST(ParserSection6, Sec6_11_AutomaticLifetimeInt) {
  auto r = Parse(
      "module t;\n"
      "  function static int get_temp();\n"
      "    automatic int temp = 42;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

// 23. reg with packed dimensions.
TEST(ParserSection6, Sec6_11_2_RegWithPackedDims) {
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

// 24. reg with signed qualifier.
TEST(ParserSection6, Sec6_11_2_RegSignedQualifier) {
  auto r = Parse(
      "module t;\n"
      "  reg signed [7:0] sr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

// =============================================================================
// LRM section 6.11 -- Integer types coexisting with real types
// =============================================================================

// 25. Integer types coexisting with real types in the same module.
TEST(ParserSection6, Sec6_11_IntegerAndRealCoexist) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "  real voltage;\n"
      "  byte flags;\n"
      "  shortreal gain;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kShortreal);
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

// =============================================================================
// LRM section 6.11 -- Integer types in generate blocks
// =============================================================================

// 28. Integer types in generate blocks.
TEST(ParserSection6, Sec6_11_IntegerTypesInGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  generate\n"
              "    genvar i;\n"
              "    for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
              "      int local_count;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 6.11 -- Comprehensive signed/unsigned qualifiers
// =============================================================================

// 29. All integer types with explicit signed/unsigned qualifiers.
TEST(ParserSection6, Sec6_11_AllTypesExplicitSignedness) {
  auto r = Parse(
      "module t;\n"
      "  byte signed bs;\n"
      "  byte unsigned bu;\n"
      "  shortint signed ss;\n"
      "  shortint unsigned su;\n"
      "  int signed is_;\n"
      "  int unsigned iu;\n"
      "  longint signed ls;\n"
      "  longint unsigned lu;\n"
      "  integer signed igs;\n"
      "  integer unsigned igu;\n"
      "  time signed ts;\n"
      "  time unsigned tu;\n"
      "  logic signed lgs;\n"
      "  logic unsigned lgu;\n"
      "  bit signed bts;\n"
      "  bit unsigned btu;\n"
      "  reg signed rs;\n"
      "  reg unsigned ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 18u);
  // byte signed / byte unsigned
  EXPECT_TRUE(items[0]->data_type.is_signed);
  EXPECT_FALSE(items[1]->data_type.is_signed);
  // shortint signed / shortint unsigned
  EXPECT_TRUE(items[2]->data_type.is_signed);
  EXPECT_FALSE(items[3]->data_type.is_signed);
  // int signed / int unsigned
  EXPECT_TRUE(items[4]->data_type.is_signed);
  EXPECT_FALSE(items[5]->data_type.is_signed);
  // longint signed / longint unsigned
  EXPECT_TRUE(items[6]->data_type.is_signed);
  EXPECT_FALSE(items[7]->data_type.is_signed);
  // integer signed / integer unsigned
  EXPECT_TRUE(items[8]->data_type.is_signed);
  EXPECT_FALSE(items[9]->data_type.is_signed);
  // time signed / time unsigned
  EXPECT_TRUE(items[10]->data_type.is_signed);
  EXPECT_FALSE(items[11]->data_type.is_signed);
  // logic signed / logic unsigned
  EXPECT_TRUE(items[12]->data_type.is_signed);
  EXPECT_FALSE(items[13]->data_type.is_signed);
  // bit signed / bit unsigned
  EXPECT_TRUE(items[14]->data_type.is_signed);
  EXPECT_FALSE(items[15]->data_type.is_signed);
  // reg signed / reg unsigned
  EXPECT_TRUE(items[16]->data_type.is_signed);
  EXPECT_FALSE(items[17]->data_type.is_signed);
}

// =============================================================================
// LRM section 6.11 -- Integer types as port declarations
// =============================================================================

// 30. Integer types as module port declarations.
TEST(ParserSection6, Sec6_11_IntegerTypesAsPortDecls) {
  auto r = Parse(
      "module m(input int a, output byte b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(ports[0].name, "a");
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(ports[1].name, "b");
}

// 30b. More integer types as ports: longint and shortint.
TEST(ParserSection6, Sec6_11_LongintShortintAsPorts) {
  auto r = Parse(
      "module m(input longint addr, output shortint result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(ports[0].name, "addr");
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(ports[1].name, "result");
}

// 30c. Integer type port with packed dimensions.
TEST(ParserSection6, Sec6_11_LogicPackedDimsAsPort) {
  auto r = Parse(
      "module m(input logic [7:0] data, output logic [15:0] addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[1].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[1].data_type.packed_dim_left->int_val, 15u);
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

// reg unsigned override.
TEST(ParserSection6, Sec6_11_2_RegUnsignedExplicit) {
  auto r = Parse(
      "module t;\n"
      "  reg unsigned [7:0] ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
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

// Integer type with unpacked dimension using range notation.
TEST(ParserSection6, Sec6_11_IntUnpackedRangeNotation) {
  auto r = Parse(
      "module t;\n"
      "  int data [0:7];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->unpacked_dims.empty());
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

// integer (4-state) as port declaration.
TEST(ParserSection6, Sec6_11_IntegerAsPort) {
  auto r = Parse(
      "module m(input integer idx);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
}
