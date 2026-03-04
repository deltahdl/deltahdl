// §6.12: Real, shortreal, and realtime data types

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection6, ShortrealInit) {
  // §6.12: shortreal is a 32-bit IEEE float.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  shortreal sr = 1.5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  ASSERT_NE(item->init_expr, nullptr);
}

}  // namespace
