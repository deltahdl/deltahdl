// §7.8.1: Wildcard index type


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_parser.h"

using namespace delta;

};

namespace {

// ---------------------------------------------------------------------------
// associative_dimension ::= [ data_type ] | [ * ]
// ---------------------------------------------------------------------------
TEST(ParserA25, AssocDimWildcard) {
  auto r = Parse("module m; int aa [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}

}  // namespace
