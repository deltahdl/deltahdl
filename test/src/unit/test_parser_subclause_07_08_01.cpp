#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DeclarationRangeParsing, AssocDimWildcard) {
  auto r = Parse("module m; int aa [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}

TEST(AggregateTypeParsing, AssocArrayWildcard) {
  auto r = Parse(
      "module t;\n"
      "  integer aa[*];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(DeclarationRangeParsing, AssocWildcardDimStartsAtItsStar) {
  auto r = Parse(
      "module m;\n"
      "  int aa [*];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->text, "*");
  EXPECT_EQ(dim->range.start.line, 2u);
  EXPECT_EQ(dim->range.start.column, 11u);
}

}  // namespace
