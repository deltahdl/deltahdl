// §7.3.1: Packed unions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA221, StructUnionUnionSoft) {
  auto r = Parse(
      "module m;\n"
      "  union soft { int a; real b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_soft);
}

}  // namespace
