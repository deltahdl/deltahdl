#include <gtest/gtest.h>

#include <cstdint>
#include <format>
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

// §7.4.2: the single-number `[size]` form is likewise a clean constant integer
// expression, so an x/z bit in it is rejected too. This drives the non-range
// branch of the check, distinct from the range-form bounds above.
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

// §7.4.2 admits any constant_expression as an unpacked bound, and §11.2.1
// lists a parameter as a constant form. The `[size]` form built from a
// parameter must resolve in the module's parameter scope, not silently
// collapse to zero. The literal-only tests above never exercised that scope.
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

// §7.4.2 range form `[constant_expression : constant_expression]` with a
// parameter in the bound, matching the packed-dimension parameter handling.
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

// §11.2.1 also lists a localparam as a constant form usable in the bound.
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

// §7.4.2 range form with a localparam in the bound — the same constant-form
// admission as the parameter range case, exercised through a localparam.
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

// §7.4.2 forms an unpacked array from any data type, including a packed array
// element (§7.4.1). The unpacked dimension sizes the outer array while the
// element keeps its full packed width — here a 4x8 packed element is 32 bits
// wide and the array holds two of them.
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

// Each dimension of a multidimensional fixed-size unpacked array carries its
// own constant_expression, so per-dimension extents built from parameters must
// resolve too (the simulator reads var.unpacked_dim_sizes).
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

// §7.4.2 requires the `[size]` form to be a positive constant integer; a
// parameter that evaluates to zero is the negative form of that rule and must
// be diagnosed once the bound is resolved in scope.
TEST(UnpackedArrayValidation, ZeroValuedParameterSizeFormRejected) {
  ElabFixture f;
  ElaborateSrc("module top; parameter int Z = 0; int x [Z]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked dimension size shall be a positive integer", 1, "7.4.2"));
}

// §7.4.2 writes a fixed-size unpacked dimension as a range of element
// addresses, and §11.5.2 rules that the bounds the memory's declaration gives
// decide what an address expression reaches, so both values written are part of
// the declaration. The elaborator records only `std::min` of each pair, in
// `unpacked_dim_los`, and only from two dimensions up; of `[3:1]` it keeps the
// 1 and the declared 3 is gone.
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

// §7.4.2 lets the first value of a dimension's range be greater than, equal to
// or less than the second, so `[3:1]` and `[1:3]` are two different
// declarations and the record has to tell them apart. Both collapse to
// `std::min` of the pair, which is 1 for either, so the two declarations leave
// the same `unpacked_dim_los`.
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

// §7.4.2 gives a multidimensional fixed-size unpacked array one range per
// dimension, so how many dimensions the declaration wrote is part of what was
// declared. `RtlirVariable` carries no count of them at all: `unpacked_dims`
// and `unpacked_dim_sizes` hold an entry only for a dimension whose bounds
// folded to constants, so the number written can only be guessed from a vector
// that a dimension can be missing from.
TEST(UnpackedArrayValidation, DeclaredDimensionCountIsRecorded) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; logic [7:0] x [1:4][2:5]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].num_unpacked_dims, 2u);
}

// The dimension §7.4.2 admits and the vector cannot hold. `[]` is a dynamic
// dimension, and the parser pushes a null dimension for it, so no entry for it
// can reach `unpacked_dims`. With no count recorded, `logic [7:0] x [1:4][]`
// and `logic [7:0] x [1:4]` leave the same one-entry record, and §11.5.2
// addressing cannot tell how many addresses a select has to supply.
TEST(UnpackedArrayValidation,
     DynamicSecondDimensionIsNotRecordedAsOneDimension) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] x [1:4][]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].num_unpacked_dims, 2u);
}

// §7.4.2 admits any constant expression as an element address bound, so a bound
// may be negative -- `NegativeBoundYieldsCorrectSize` above elaborates the same
// declaration and asks only for its size. §11.5.2 makes the declared bounds
// decide which element an address names, and `unpacked_lo` is `uint32_t`, so
// -3 is recorded as 4294967293 and every address computed from it is wrong.
TEST(UnpackedArrayValidation, NegativeLowBoundIsRecordedAsDeclared) {
  ElabFixture f;
  auto* design = Elaborate("module m; int x [-3:5]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  ASSERT_EQ(mod->variables[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_dims[0].left, -3);
}

// §7.4.2 draws no distinction between a one-dimensional unpacked array and a
// multidimensional one: each dimension is a range of element addresses, and a
// declaration with one dimension wrote one such range. The per-dimension record
// is filled only from two dimensions up, so `[1:4]` leaves it empty and its
// declared bounds survive only as `std::min` of the pair in `unpacked_lo`.
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

// A.2.5 and §7.4.2: an unpacked dimension's bounds, and a queue's, are
// constant expressions, and a variable, a net and a const variable, set at run
// time (§6.20.6), are none. Each dimension below reads one, at module scope or
// in a block, and is reported. Each was accepted, and its declaration built
// with no dimension.
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

// Parameters, a package's parameter, `$size` of a fixed-size array, a type
// reference, a constant function's call, and a block's own local parameter
// hiding the module's variable of its name each leave a dimension constant,
// in a block and a fork alike, and draw no report.
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

}  // namespace
