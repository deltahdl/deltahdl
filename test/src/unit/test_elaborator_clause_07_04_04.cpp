#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.4.4: Multiple packed dims produce correct total width.
TEST(MultidimensionalArrayValidation, MultiPackedDimWidth) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; bit [3:0] [7:0] joe [1:10]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

// §7.4.4: Two-dim unpacked array elaborates without error.
TEST(MultidimensionalArrayValidation, TwoDimUnpackedElaborates) {
  ElabFixture f;
  auto* design = Elaborate("module m; int matrix[4][8]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
}

// §7.4.4: Comma-separated declarations share packed dims.
TEST(MultidimensionalArrayValidation, CommaSeparatedSharePackedDims) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; bit [7:0] v7 [1:5], v8 [0:255]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, mod->variables[1].width);
}

}  // namespace
