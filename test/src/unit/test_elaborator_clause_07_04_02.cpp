#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UnpackedArrayValidation, UnpackedDimElaboratesRange) {
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

TEST(UnpackedArrayValidation, UnpackedDimElaboratesSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic x [8]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
}

TEST(UnpackedArrayValidation, AscendingUnpackedRange) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic x [0:7]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
  EXPECT_FALSE(mod->variables[0].is_descending);
}

TEST(UnpackedArrayValidation, LeftBoundXzRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x [1'bx:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnpackedArrayValidation, RightBoundXzRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x [7:1'bz];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnpackedArrayValidation, RangeAndSizeFormEquivalent) {
  ElabFixture f1;
  auto* d1 = Elaborate("module m; int x [0:7]; endmodule\n", f1);
  ASSERT_NE(d1, nullptr);

  ElabFixture f2;
  auto* d2 = Elaborate("module m; int x [8]; endmodule\n", f2);
  ASSERT_NE(d2, nullptr);

  const auto& a = d1->top_modules[0]->variables[0];
  const auto& b = d2->top_modules[0]->variables[0];
  EXPECT_EQ(a.unpacked_size, b.unpacked_size);
  EXPECT_EQ(a.unpacked_lo, b.unpacked_lo);
  EXPECT_EQ(a.is_descending, b.is_descending);
}

TEST(UnpackedArrayValidation, SizeFormDefaultsToAscendingFromZero) {
  ElabFixture f;
  auto* design = Elaborate("module m; int x [5]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 5u);
  EXPECT_EQ(mod->variables[0].unpacked_lo, 0u);
  EXPECT_FALSE(mod->variables[0].is_descending);
}

TEST(UnpackedArrayValidation, NegativeBoundYieldsCorrectSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; int x [-3:5]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 9u);
}

TEST(UnpackedArrayValidation, ZeroBoundYieldsCorrectSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; int x [0:0]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 1u);
}

TEST(UnpackedArrayValidation, ZeroSizeFormRejected) {
  ElabFixture f;
  ElaborateSrc("module top; int x [0]; endmodule\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnpackedArrayValidation, NegativeSizeFormRejected) {
  ElabFixture f;
  ElaborateSrc("module top; int x [-3]; endmodule\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnpackedArrayValidation, LargeArraySupportsAtLeastTwoPowTwentyFour) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic x [16777216]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 16777216u);
}

TEST(UnpackedArrayValidation, TwoDimUnpackedElaborates) {
  ElabFixture f;
  auto* design = Elaborate("module m; int x [3][4]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_GT(mod->variables[0].unpacked_size, 0u);
}

}  // namespace
