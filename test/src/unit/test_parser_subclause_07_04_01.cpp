#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(PackedArrayParsing, MultiplePackedDims) {
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

TEST(PackedArrayParsing, ConstantRangeInPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

TEST(PackedArrayParsing, SingleNumberDimIsError) {
  auto r = Parse("module m; logic [8] x; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ':', got ']'", 1, "7.4.1"));
}

TEST(PackedArrayParsing, SignedPackedArray) {
  auto r = Parse(
      "module m;\n"
      "  logic signed [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(PackedArrayParsing, FirstDimMissingBracketNames7_4_1) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0 x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']'", 2, "7.4.1"));
}

TEST(PackedArrayParsing, SecondDimMissingBracketNames7_4_1) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0][7:0 x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']'", 2, "7.4.1"));
}

TEST(PackedArrayParsing, EnumPackedDimMissingBracketNames7_4_1) {
  auto r = Parse(
      "module m;\n"
      "  enum { A } [7:0 e;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']'", 2, "7.4.1"));
}

TEST(PackedArrayParsing, EnumDimsAfterTheBodyKeepTheBaseTypesOwn) {
  auto r = Parse(
      "module t;\n"
      "  enum bit [1:0] {A, B, C} [3:0][4:1] v;\n"
      "  typedef enum {P, Q} [2:0] e_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 2u);
  const DataType& v = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(v.kind, DataTypeKind::kEnum);
  ASSERT_NE(v.packed_dim_left, nullptr);
  EXPECT_EQ(v.packed_dim_left->int_val, 1u);
  EXPECT_TRUE(v.extra_packed_dims.empty());
  ASSERT_EQ(v.enum_array_dims.size(), 2u);
  EXPECT_EQ(v.enum_array_dims[0].first->int_val, 3u);
  EXPECT_EQ(v.enum_array_dims[1].second->int_val, 1u);
  const DataType& e = r.cu->modules[0]->items[1]->typedef_type;
  EXPECT_EQ(e.kind, DataTypeKind::kEnum);
  EXPECT_EQ(e.packed_dim_left, nullptr);
  ASSERT_EQ(e.enum_array_dims.size(), 1u);
  EXPECT_EQ(e.enum_array_dims[0].first->int_val, 2u);
}

TEST(PackedArrayParsing, VirtualInterfaceTakesNoPackedDimension) {
  auto r = Parse(
      "interface I; endinterface\n"
      "module m;\n"
      "  virtual I v;\n"
      "  virtual I [1:0] w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got '['", 4, "6.8"));
}

}  // namespace
