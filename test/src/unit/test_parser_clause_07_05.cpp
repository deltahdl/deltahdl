// §7.5: Dynamic arrays


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_parser.h"

using namespace delta;

};

namespace {

// ---------------------------------------------------------------------------
// unsized_dimension ::= [ ]
// ---------------------------------------------------------------------------
TEST(ParserA25, UnsizedDimDynamicArray) {
  auto r = Parse("module m; int d []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

}  // namespace
