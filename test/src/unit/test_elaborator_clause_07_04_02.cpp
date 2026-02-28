// §7.4.2: Unpacked arrays


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, UnpackedDimElaboratesRange) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic x [3:0]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].unpacked_size, 4u);
  EXPECT_EQ(mod->variables[0].unpacked_lo, 0u);
  EXPECT_TRUE(mod->variables[0].is_descending);
}

TEST(ParserA25, UnpackedDimElaboratesSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic x [8]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
}

TEST(ParserA25, AscendingUnpackedRange) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic x [0:7]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
  EXPECT_FALSE(mod->variables[0].is_descending);
}

}  // namespace
