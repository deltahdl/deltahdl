// §6.9

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §6.9: Scalar — no range specification, 1-bit wide.
TEST(ParserSection6, Sec6_9_ScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

}  // namespace
