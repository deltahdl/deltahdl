#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(MultidimensionalArrayValidation, TwoDimUnpackedElaborates) {
  ElabFixture f;
  auto* design = Elaborate("module m; int matrix[4][8]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
}

TEST(MultidimensionalArrayValidation, PackedDimsViaTypedefStaging) {
  // §7.4.4: multiple packed dimensions may be assembled in stages through a
  // typedef. The packed range carried by the typedef supplies the element
  // width, while the unpacked range at the use site sizes the array.
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix v5 [1:10];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirVariable* v5 = nullptr;
  for (const auto& v : mod->variables) {
    if (v.name == "v5") v5 = &v;
  }
  ASSERT_NE(v5, nullptr);
  EXPECT_EQ(v5->width, 5u);
  EXPECT_EQ(v5->unpacked_size, 10u);
}

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
