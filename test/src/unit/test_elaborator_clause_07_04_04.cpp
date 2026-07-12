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

TEST(MultidimensionalArrayValidation, PackedDimsViaTypedefStagingCombineWidth) {
  // §7.4.4: multiple packed dimensions may be assembled in stages with a
  // typedef. A packed range placed before the name at the use site of the
  // typedef stacks on top of the typedef's own packed range, so v5 declared as
  // `bsix [1:10] v5` (bsix == bit [1:5]) is a single 50-bit packed value, not a
  // 10-element unpacked array of 5-bit words.
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix [1:10] v5;\n"
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
  EXPECT_EQ(v5->width, 50u);
  // The staged dimension is packed, not unpacked: v5 is a single scalar packed
  // word rather than an array of elements.
  EXPECT_EQ(v5->unpacked_size, 0u);
}

TEST(MultidimensionalArrayValidation, MultiPackedDimWidthParameterBounds) {
  // §7.4.4: the two packed dimensions of an array of arrays combine into the
  // element width. Each dimension bound is a constant expression; when a
  // parameter supplies the bound it is resolved through the parameter scope
  // (a different width-evaluation path than a plain literal), and both packed
  // ranges must still multiply into the element width (4 * 8 == 32 here).
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int P = 4;\n"
      "  parameter int Q = 8;\n"
      "  bit [P-1:0] [Q-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirVariable* w = nullptr;
  for (const auto& v : mod->variables) {
    if (v.name == "w") w = &v;
  }
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 32u);
}

TEST(MultidimensionalArrayValidation,
     PackedDimsViaTypedefStagingParameterWidth) {
  // §7.4.4: the packed dimension staged onto a typedef at its use site is a
  // constant expression. A parameter as that bound resolves through the
  // parameter scope, exercising the scope-aware branch of the staging-width
  // rule rather than the literal branch, yet must still combine to 50 bits
  // (10 elements of the typedef's own 5-bit packed range).
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int P = 10;\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix [1:P] v5;\n"
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
  EXPECT_EQ(v5->width, 50u);
}

TEST(MultidimensionalArrayValidation,
     PackedDimsViaTypedefStagingLocalparamWidth) {
  // §7.4.4: a localparam bound on the staged packed dimension is likewise a
  // constant expression and combines identically to a literal or parameter
  // bound, giving the full 50-bit width.
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int R = 10;\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix [1:R] v5;\n"
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
  EXPECT_EQ(v5->width, 50u);
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
