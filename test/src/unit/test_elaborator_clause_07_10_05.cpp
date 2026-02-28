// §7.10.5: Bounded queues


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, QueueDimElaboratesBounded) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:255]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 256);
}

}  // namespace
