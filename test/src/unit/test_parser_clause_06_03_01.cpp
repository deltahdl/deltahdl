#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §6.3.1 ¶4: `logic` declares an object of the basic 4-state data type. The
// parser must record the variable's data type as DataTypeKind::kLogic.
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

// §6.3.1 ¶4: `logic` may carry a packed dimension to declare a vector of the
// basic 4-state type. The parser must still record kLogic and preserve the
// packed-range expressions for the elaborator.
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

// §6.3.1 ¶4: `logic` may be used to construct other data types — here, a
// typedef built from `logic`. The parser must accept the construction without
// errors so that the elaborator can derive the user type from the 4-state
// base.
TEST(LogicValuesParser, TypedefBuiltFromLogicParses) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic [7:0] my_byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
