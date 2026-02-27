// §6.6: Net types

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2NetDeclTriWandWor) {
  auto r = Parse("module m; tri t; wand wa; wor wo; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 3u);
}

}  // namespace
