// §7.4.3: Memories

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, PackedAndUnpackedElaboration) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] mem [0:3]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 4u);
}

}  // namespace
