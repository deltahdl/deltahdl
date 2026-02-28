// §7.4.4: Multidimensional arrays

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA25, UnpackedDimMultiple) {
  auto r = Parse("module m; logic x [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 2u);
}

}  // namespace
