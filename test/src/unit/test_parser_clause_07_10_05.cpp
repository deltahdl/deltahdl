// §7.10.5: Bounded queues


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_parser.h"

using namespace delta;

};

namespace {

TEST(ParserA25, QueueDimBounded) {
  auto r = Parse("module m; int q [$:100]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  ASSERT_NE(item->unpacked_dims[0]->rhs, nullptr);
}

}  // namespace
