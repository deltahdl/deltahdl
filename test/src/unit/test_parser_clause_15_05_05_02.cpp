#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(NamedEventParser, EventInitializedToNull) {
  auto r = Parse(
      "module m;\n"
      "  event empty = null;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
