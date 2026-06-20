#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(QueueDeclarationParsing, QueueDimBounded) {
  auto r = Parse("module m; int q [$:100]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  ASSERT_NE(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(QueueDeclarationParsing, QueueBounded) {
  auto r = Parse(
      "module t;\n"
      "  bit q2[$:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "q2");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

}  // namespace
