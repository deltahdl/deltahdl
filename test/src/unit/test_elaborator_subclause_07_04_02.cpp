#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string_view>
#include <utility>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension range shall not contain x or z",
                            2, "7.4.2"));
}

TEST(UnpackedArrayValidation, RightBoundXzRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x [7:1'bz];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension range shall not contain x or z",
                            2, "7.4.2"));
}

TEST(UnpackedArrayValidation, SizeFormXzRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x [1'bx];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension range shall not contain x or z",
                            2, "7.4.2"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked dimension size shall be a positive integer", 1, "7.4.2"));
}

TEST(UnpackedArrayValidation, NegativeSizeFormRejected) {
  ElabFixture f;
  ElaborateSrc("module top; int x [-3]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked dimension size shall be a positive integer", 1, "7.4.2"));
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

TEST(UnpackedArrayValidation, ParameterSizedUnpackedDimResolves) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; parameter int N = 8; logic x [N]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
}

TEST(UnpackedArrayValidation, ParameterRangeUnpackedDimResolves) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m; parameter int N = 8; logic x [N-1:0]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
  EXPECT_EQ(mod->variables[0].unpacked_lo, 0u);
  EXPECT_TRUE(mod->variables[0].is_descending);
}

TEST(UnpackedArrayValidation, LocalparamSizedUnpackedDimResolves) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; localparam M = 4; int x [M]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 4u);
}

TEST(UnpackedArrayValidation, LocalparamRangeUnpackedDimResolves) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; localparam M = 8; logic x [M-1:0]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
  EXPECT_EQ(mod->variables[0].unpacked_lo, 0u);
  EXPECT_TRUE(mod->variables[0].is_descending);
}

TEST(UnpackedArrayValidation, PackedArrayElementArrayElaborates) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; logic [3:0][7:0] mem [2]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 2u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

TEST(UnpackedArrayValidation, ParameterMultiDimUnpackedResolves) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m; parameter int N = 3; parameter int P = 5; int x [N][P]; "
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  ASSERT_EQ(mod->variables[0].unpacked_dim_sizes.size(), 2u);
  EXPECT_EQ(mod->variables[0].unpacked_dim_sizes[0], 3u);
  EXPECT_EQ(mod->variables[0].unpacked_dim_sizes[1], 5u);
}

TEST(UnpackedArrayValidation, ZeroValuedParameterSizeFormRejected) {
  ElabFixture f;
  ElaborateSrc("module top; parameter int Z = 0; int x [Z]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked dimension size shall be a positive integer", 1, "7.4.2"));
}

TEST(UnpackedArrayValidation, EachDimensionKeepsBothDeclaredBounds) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; logic [7:0] x [1:2][3:1]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  ASSERT_EQ(mod->variables[0].unpacked_dims.size(), 2u);
  EXPECT_EQ(std::make_pair(mod->variables[0].unpacked_dims[1].left,
                           mod->variables[0].unpacked_dims[1].right),
            std::make_pair(int64_t{3}, int64_t{1}));
}

TEST(UnpackedArrayValidation, OppositeSecondDimensionRecordsDifferently) {
  ElabFixture f1;
  auto* d1 = Elaborate("module m; logic [7:0] x [1:2][3:1]; endmodule\n", f1);
  ASSERT_NE(d1, nullptr);

  ElabFixture f2;
  auto* d2 = Elaborate("module m; logic [7:0] x [1:2][1:3]; endmodule\n", f2);
  ASSERT_NE(d2, nullptr);

  const auto& a = d1->top_modules[0]->variables[0];
  const auto& b = d2->top_modules[0]->variables[0];
  ASSERT_EQ(a.unpacked_dims.size(), 2u);
  ASSERT_EQ(b.unpacked_dims.size(), 2u);
  EXPECT_NE(std::make_pair(a.unpacked_dims[1].left, a.unpacked_dims[1].right),
            std::make_pair(b.unpacked_dims[1].left, b.unpacked_dims[1].right));
}

TEST(UnpackedArrayValidation, DeclaredDimensionCountIsRecorded) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; logic [7:0] x [1:4][2:5]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].num_unpacked_dims, 2u);
}

TEST(UnpackedArrayValidation,
     DynamicSecondDimensionIsNotRecordedAsOneDimension) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] x [1:4][]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].num_unpacked_dims, 2u);
}

TEST(UnpackedArrayValidation, NegativeLowBoundIsRecordedAsDeclared) {
  ElabFixture f;
  auto* design = Elaborate("module m; int x [-3:5]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  ASSERT_EQ(mod->variables[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_dims[0].left, -3);
}

TEST(UnpackedArrayValidation, SingleDimensionFillsThePerDimensionRecord) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] x [1:4]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  ASSERT_EQ(mod->variables[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(std::make_pair(mod->variables[0].unpacked_dims[0].left,
                           mod->variables[0].unpacked_dims[0].right),
            std::make_pair(int64_t{1}, int64_t{4}));
}

TEST(UnpackedArrayValidation, VariableReadInUnpackedDimIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int n;\n"
      "  const int k = 2;\n"
      "  wire [3:0] v;\n"
      "  int a [n];\n"
      "  logic [7:0] b [0:n];\n"
      "  wire w [n];\n"
      "  int q [$:v];\n"
      "  int g [k];\n"
      "  initial begin\n"
      "    int c [n];\n"
      "  end\n"
      "endmodule\n",
      f);
  const struct {
    const char* declared;
    const char* read;
    uint32_t line;
  } kReads[] = {{"a", "n", 5}, {"b", "n", 6}, {"w", "n", 7},
                {"q", "v", 8}, {"g", "k", 9}, {"c", "n", 11}};
  for (const auto& read : kReads) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("unpacked dimension of '{}' reads '{}', which is no "
                    "constant, so the dimension is not a constant expression",
                    read.declared, read.read),
        read.line, "7.4.2"))
        << read.declared;
  }
}

TEST(UnpackedArrayValidation, ConstantsInUnpackedDimsAreNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p; parameter int N = 3; endpackage\n"
      "module m;\n"
      "  parameter int P = 4;\n"
      "  localparam int L = 2;\n"
      "  int n;\n"
      "  int fixed [4];\n"
      "  int s [$size(fixed)];\n"
      "  int t [p::N];\n"
      "  int u [type(n)];\n"
      "  int d [P];\n"
      "  int e [0:L];\n"
      "  function int f(int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  int h [f(2)];\n"
      "  initial begin\n"
      "    typedef int word_t;\n"
      "    localparam int n = 2;\n"
      "    int c [n];\n"
      "    fork\n"
      "      int z [L];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  const struct {
    const char* declared;
    uint32_t line;
  } kDims[] = {{"s", 7},  {"t", 8},  {"u", 9},  {"d", 10},
               {"e", 11}, {"h", 15}, {"c", 19}, {"z", 21}};
  for (const auto& dim : kDims) {
    EXPECT_FALSE(ReportedError(
        f.diag.Diagnostics(),
        std::format("unpacked dimension of '{}' reads", dim.declared), dim.line,
        "7.4.2"))
        << dim.declared;
  }
}

constexpr std::string_view kXz =
    "unpacked dimension range shall not contain x or z";
constexpr std::string_view kSize =
    "unpacked dimension size shall be a positive integer";

TEST(UnpackedArrayValidation,
     XzBoundAndNonPositiveSizeReportedInInterfaceProgramCheckerAndGenerate) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  logic i1 [0:1'bx];\n"
      "  logic i2 [0];\n"
      "  logic i3 [4];\n"
      "  logic i4 [3:0];\n"
      "endinterface\n"
      "program pr;\n"
      "  logic r1 [1'bx:0];\n"
      "  logic r2 [-1];\n"
      "  logic r3 [4];\n"
      "endprogram\n"
      "checker ck;\n"
      "  logic k1 [2'bz1:0];\n"
      "  logic k2 [0];\n"
      "  logic k3 [4];\n"
      "endchecker\n"
      "module top;\n"
      "  ifc ii();\n"
      "  pr p();\n"
      "  ck c();\n"
      "  if (1) begin : g\n"
      "    logic g1 [1'bx:0];\n"
      "    logic g2 [0];\n"
      "    logic g3 [4];\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2, 8, 13, 22}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXz, line, "7.4.2"))
        << line;
  }
  for (uint32_t line : {3, 9, 14, 23}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kSize, line, "7.4.2"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 8u);
}

TEST(UnpackedArrayValidation,
     DISABLED_XzBoundAndNonPositiveSizeReportedOutsideModuleScopes) {
  ElabFixture f;
  ElaborateSrc(
      "logic cu1 [1'bx:0];\n"
      "logic cu2 [0];\n"
      "logic cu3 [4];\n"
      "package pk;\n"
      "  logic p1 [2'bz1:0];\n"
      "  logic p2 [-1];\n"
      "  logic p3 [3:0];\n"
      "endpackage\n"
      "class C;\n"
      "  logic c1 [1'bx:0];\n"
      "  static logic c2 [0];\n"
      "  logic c3 [4];\n"
      "endclass\n"
      "typedef struct {\n"
      "  logic s1 [1'bx:0];\n"
      "  logic s2 [0];\n"
      "  logic s3 [4];\n"
      "} us_t;\n"
      "module top;\n"
      "  function automatic void f(input logic fa [0]);\n"
      "    logic f1 [1'bx:0];\n"
      "    logic f2 [-2];\n"
      "    logic f3 [4];\n"
      "  endfunction\n"
      "  task automatic t;\n"
      "    logic t1 [0:1'bz];\n"
      "    logic t2 [0];\n"
      "    logic t3 [4];\n"
      "  endtask\n"
      "  initial begin\n"
      "    logic b1 [1'bx:0];\n"
      "    logic b2 [0];\n"
      "    logic b3 [4];\n"
      "  end\n"
      "  us_t s;\n"
      "  typedef logic td1 [1'bx:0];\n"
      "  typedef logic td2 [0];\n"
      "  typedef logic td3 [4];\n"
      "endmodule\n",
      f);
  for (uint32_t line : {1, 5, 10, 15, 21, 26, 31, 36}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kXz, line, "7.4.2"))
        << line;
  }
  for (uint32_t line : {2, 6, 11, 16, 20, 22, 27, 32, 37}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kSize, line, "7.4.2"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 17u);
}

}  // namespace
