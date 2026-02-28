// §7.4.3: Memories

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;
}
;

namespace {

// ---------------------------------------------------------------------------
// Combined / edge cases
// ---------------------------------------------------------------------------
TEST(ParserA25, PackedAndUnpackedDims) {
  auto r = Parse("module m; logic [7:0] mem [0:255]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

}  // namespace
