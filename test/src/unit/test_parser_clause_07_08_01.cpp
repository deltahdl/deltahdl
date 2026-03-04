// §7.8.1: Wildcard index type

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// associative_dimension ::= [ data_type ] | [ * ]
// ---------------------------------------------------------------------------
TEST(ParserA25, AssocDimWildcard) {
  auto r = Parse("module m; int aa [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}
// =========================================================================
// §7.8: Associative arrays
// =========================================================================
TEST(ParserSection7, AssocArrayWildcard) {
  auto r = Parse("module t;\n"
                 "  integer aa[*];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
  EXPECT_FALSE(item->unpacked_dims.empty());
}
// --- Test helpers ---
// =========================================================================
// §7.8: Associative arrays
// =========================================================================
TEST(ParserSection7, AssociativeArrayWildcardIndex) {
  auto r = Parse("module t;\n"
                 "  int aa[*];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
}

} // namespace
