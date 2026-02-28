// §7.8.4: Integral index

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;
}
;

namespace {

TEST(ParserA25, AssocDimIntType) {
  auto r = Parse("module m; logic [7:0] aa [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(ParserA25, AssocDimByteType) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
}

}  // namespace
