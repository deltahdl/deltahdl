#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LogicValuesParser, LogicScalarDeclarationParsesAsKLogic) {
  auto r = Parse(
      "module t;\n"
      "  logic v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "v");
}

TEST(LogicValuesParser, LogicVectorDeclarationParsesAsKLogicWithPackedDim) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(LogicValuesParser, TypedefBuiltFromLogicParses) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic [7:0] my_byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
