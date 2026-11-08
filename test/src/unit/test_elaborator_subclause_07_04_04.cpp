#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"

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
  EXPECT_EQ(v5->unpacked_size, 0u);
}

TEST(MultidimensionalArrayValidation, MultiPackedDimWidthParameterBounds) {
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

TEST(StagedPackedDimensions, PackageParameterOfATypedefWithDimensionsIsNotCut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [3:0] nib;\n"
      "  parameter nib [1:0] P = 8'hFF;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int Q = p::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 255);
}

TEST(StagedPackedDimensions, ClassParameterOfATypedefWithDimensionsIsNotCut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef bit [3:0] nib;\n"
      "class C #(nib [1:0] P = 8'hFF);\n"
      "endclass\n"
      "module m;\n"
      "  localparam int Q = C#()::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 255);
}

}  // namespace
