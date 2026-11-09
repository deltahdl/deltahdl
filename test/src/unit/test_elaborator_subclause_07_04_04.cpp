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

TEST(MultidimensionalArrayValidation, ParameterSelectsFoldToTheSubarray) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [3:0] nib_t;\n"
      "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
      "typedef struct {\n"
      "  logic [1:0][3:0] q;\n"
      "  ps_t [1:0] pa;\n"
      "  logic [1:0][3:0] u [2];\n"
      "} us_t;\n"
      "module m;\n"
      "  parameter logic [1:0][3:0] Q = 8'h6C;\n"
      "  parameter logic [0:1][3:0] A = 8'h6C;\n"
      "  parameter logic [1:0][1:0][3:0] R = 16'h1234;\n"
      "  parameter nib_t [1:0] T = 8'h6C;\n"
      "  parameter ps_t [1:0] PA = 16'h1234;\n"
      "  parameter us_t P = '{q: 8'h6C, pa: 16'h1234, u: '{8'h6C, 8'h12}};\n"
      "  parameter logic [1:0][3:0] E [2] = '{8'h6C, 8'h12};\n"
      "  parameter struct packed {\n"
      "    ps_t [1:0][1:0] pq;\n"
      "    logic [1:0][1:0][3:0] n;\n"
      "  } M = 48'h12345678_5a3c;\n"
      "  parameter struct packed {\n"
      "    struct packed { logic [3:0] hi; logic [3:0] lo; } [1:0][1:0] pb;\n"
      "    struct packed { logic [3:0] hi; logic [3:0] lo; } [1:0] pc;\n"
      "  } N = 48'h9abcdef0_7b6a;\n"
      "  parameter struct packed {\n"
      "    struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  } [1:0] SP = 16'h1234;\n"
      "  parameter union packed { logic [7:0] w; logic [1:0][3:0] n; } [1:0] "
      "UP\n"
      "      = 16'h1234;\n"
      "  localparam V1 = Q[1], V2 = Q[0], V3 = Q[1][2:1], V4 = Q[1:0];\n"
      "  localparam V5 = A[0], V6 = R[1], V7 = R[0][1], V8 = R[0][1][1];\n"
      "  localparam V9 = T[1], V10 = PA[1], V11 = PA[1].lo;\n"
      "  localparam V12 = P.q[1], V13 = P.pa[1], V14 = P.pa[1].lo;\n"
      "  localparam V15 = E[1][1], V16 = SP[1].s.lo, V17 = UP[0].n[1];\n"
      "  localparam V18 = SP[0], V19 = UP[1];\n"
      "  localparam int B1 = $bits(V1), B3 = $bits(V3), B4 = $bits(V4);\n"
      "  localparam int B6 = $bits(V6), B10 = $bits(V10), B13 = $bits(V13);\n"
      "  localparam int B18 = $bits(V18), B19 = $bits(V19);\n"
      "  localparam V20 = M.pq[1][0], V21 = M.pq[1][0].hi, V22 = "
      "N.pb[0][1].lo;\n"
      "  localparam V23 = N.pc[1].lo, V24 = M.n[1][0], V25 = M.n[0];\n"
      "  localparam V26 = P.u[1][0], V27 = P.u[0], V28 = M.pq;\n"
      "  localparam V29 = N.pc[1][2], V30 = M.n[0][1][1];\n"
      "  localparam int B20 = $bits(V20), B26 = $bits(V26), B28 = $bits(V28);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "V1"), 0x6);
  EXPECT_EQ(ParamValue(design, "V2"), 0xC);
  EXPECT_EQ(ParamValue(design, "V3"), 0x3);
  EXPECT_EQ(ParamValue(design, "V4"), 0x6C);
  EXPECT_EQ(ParamValue(design, "V5"), 0x6);
  EXPECT_EQ(ParamValue(design, "V6"), 0x12);
  EXPECT_EQ(ParamValue(design, "V7"), 0x3);
  EXPECT_EQ(ParamValue(design, "V8"), 0x1);
  EXPECT_EQ(ParamValue(design, "V9"), 0x6);
  EXPECT_EQ(ParamValue(design, "V10"), 0x12);
  EXPECT_EQ(ParamValue(design, "V11"), 0x2);
  EXPECT_EQ(ParamValue(design, "V12"), 0x6);
  EXPECT_EQ(ParamValue(design, "V13"), 0x12);
  EXPECT_EQ(ParamValue(design, "V14"), 0x2);
  EXPECT_EQ(ParamValue(design, "V15"), 0x1);
  EXPECT_EQ(ParamValue(design, "V16"), 0x2);
  EXPECT_EQ(ParamValue(design, "V17"), 0x3);
  EXPECT_EQ(ParamValue(design, "V18"), 0x34);
  EXPECT_EQ(ParamValue(design, "V19"), 0x12);
  EXPECT_EQ(ParamValue(design, "B1"), 4);
  EXPECT_EQ(ParamValue(design, "B3"), 2);
  EXPECT_EQ(ParamValue(design, "B4"), 8);
  EXPECT_EQ(ParamValue(design, "B6"), 8);
  EXPECT_EQ(ParamValue(design, "B10"), 8);
  EXPECT_EQ(ParamValue(design, "B13"), 8);
  EXPECT_EQ(ParamValue(design, "B18"), 8);
  EXPECT_EQ(ParamValue(design, "B19"), 8);
  EXPECT_EQ(ParamValue(design, "V20"), 0x34);
  EXPECT_EQ(ParamValue(design, "V21"), 0x3);
  EXPECT_EQ(ParamValue(design, "V22"), 0xE);
  EXPECT_EQ(ParamValue(design, "V23"), 0xB);
  EXPECT_EQ(ParamValue(design, "V24"), 0xA);
  EXPECT_EQ(ParamValue(design, "V25"), 0x3C);
  EXPECT_EQ(ParamValue(design, "V26"), 0x2);
  EXPECT_EQ(ParamValue(design, "V27"), 0x6C);
  EXPECT_EQ(ParamValue(design, "V28"), 0x12345678);
  EXPECT_EQ(ParamValue(design, "V29"), 0x0);
  EXPECT_EQ(ParamValue(design, "V30"), 0x1);
  EXPECT_EQ(ParamValue(design, "B20"), 8);
  EXPECT_EQ(ParamValue(design, "B26"), 4);
  EXPECT_EQ(ParamValue(design, "B28"), 32);
}

}  // namespace
