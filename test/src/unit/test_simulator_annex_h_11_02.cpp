#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

TEST(DpiMultidimensionalArrays, PackedDimensionsLinearizeToOneNormalizedRange) {
  const SvActualDimension kTwo = DpiLinearizedPackedRange({{6, 1}, {1, 8}});
  EXPECT_EQ(kTwo.low, 47);
  EXPECT_EQ(kTwo.high, 0);
  const SvActualDimension kThree =
      DpiLinearizedPackedRange({{1, 0}, {3, 0}, {7, 0}});
  EXPECT_EQ(kThree.low, 63);
  EXPECT_EQ(kThree.high, 0);
  const SvActualDimension kOne = DpiLinearizedPackedRange({{29, 0}});
  EXPECT_EQ(kOne.low, 29);
  EXPECT_EQ(kOne.high, 0);
  EXPECT_EQ(DpiPackedDimensionCountInC(), 1u);
}

TEST(DpiMultidimensionalArrays, TheLinearizedRangeIsWhatTheChunksHold) {
  EXPECT_EQ(DpiCanonicalWordCount(48), 2u);
  DpiArg b;
  b.name = "b";
  b.type = DataTypeKind::kBit;
  b.direction = Direction::kInout;
  b.width = 48;
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(b, {{65, 2}}),
            "svBitVecVal b[64][2]");
}

TEST(DpiMultidimensionalArrays, UnpackedArraysHaveAnyNumberOfDimensions) {
  EXPECT_FALSE(DpiUnpackedDimensionCountIsLimited());
  DpiArg a;
  a.name = "a";
  a.type = DataTypeKind::kInt;
  a.direction = Direction::kOutput;
  const std::vector<SvActualDimension> kFour = {{1, 0}, {2, 0}, {3, 0}, {1, 4}};
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(a, kFour), "int a[2][3][4][4]");
  const std::vector<uint32_t> kIndices =
      DpiCIndicesOfUnpackedElement(kFour, {1, 2, 3, 4});
  ASSERT_EQ(kIndices.size(), 4u);
  EXPECT_EQ(kIndices[0], 1u);
  EXPECT_EQ(kIndices[1], 2u);
  EXPECT_EQ(kIndices[2], 3u);
  EXPECT_EQ(kIndices[3], 3u);
}

TEST(DpiMultidimensionalArrays, AnOpenArrayReportsEveryUnpackedDimension) {
  const SvOpenArrayDimRange kRanges[] = {
      {47, 0}, {1, 0}, {2, 0}, {3, 0}, {1, 4}};
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = 5;
  desc.has_packed_part = 1;
  desc.ranges = kRanges;
  desc.elem_size = 0;
  svOpenArrayHandle h = &desc;
  EXPECT_EQ(svDimensions(h), 5);
  EXPECT_EQ(svSize(h, 0), 48);
  EXPECT_EQ(svSize(h, 4), 4);
}

void SeeThreeByFour(const int a[3][4]) {
  SeeInC({a[0][0], a[0][3], a[1][2], a[2][0], a[2][3]});
}

TEST(DpiMultidimensionalArrays, ATwoDimensionalInputArrives) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input int a [3:1][2:5]);\n"
      "  int a [3:1][2:5];\n"
      "  initial begin\n"
      "    foreach (a[i, j]) a[i][j] = i * 10 + j;\n"
      "    see(a);\n"
      "  end\n",
      f, {{"see", CAddress(&SeeThreeByFour)}}, "annex_h_11_02_input");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{12, 15, 24, 32, 35}));
}

void FillThreeDimensions(int a[2][3][2]) {
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      for (int k = 0; k < 2; ++k) a[i][j][k] = (i * 100) + (j * 10) + k;
    }
  }
}

TEST(DpiMultidimensionalArrays, AThreeDimensionalOutputIsWrittenBack) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void fill(\n"
      "      output int a [2:1][0:2][-1:0]);\n"
      "  int a [2:1][0:2][-1:0];\n"
      "  int first, middle, last;\n"
      "  initial begin\n"
      "    fill(a);\n"
      "    first = a[1][0][0]; middle = a[2][1][-1]; last = a[2][2][0];\n"
      "  end\n",
      f, {{"fill", CAddress(&FillThreeDimensions)}}, "annex_h_11_02_output");
  EXPECT_EQ(DesignValue(f, "first"), 1U);
  EXPECT_EQ(DesignValue(f, "middle"), 110U);
  EXPECT_EQ(DesignValue(f, "last"), 121U);
}

void AddPositions(short a[2][2][2][3]) {
  SeeInC({a[0][0][0][0], a[1][0][1][2], a[0][1][0][1]});
  a[1][0][1][2] = static_cast<short>(a[1][0][1][2] + 1000);
  a[0][1][0][1] = static_cast<short>(a[0][1][0][1] + 2000);
}

TEST(DpiMultidimensionalArrays, AFourDimensionalInoutIsReadAndWritten) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void add(\n"
      "      inout shortint a [0:1][1:0][5:4][3]);\n"
      "  shortint a [0:1][1:0][5:4][3];\n"
      "  int kept, first, second;\n"
      "  initial begin\n"
      "    foreach (a[i, j, k, l])\n"
      "      a[i][j][k][l] = i * 100 + j * 50 + k * 5 + l;\n"
      "    add(a);\n"
      "    kept = a[0][0][4][0]; first = a[1][0][5][2];\n"
      "    second = a[0][1][4][1];\n"
      "  end\n",
      f, {{"add", CAddress(&AddPositions)}}, "annex_h_11_02_inout");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{20, 127, 71}));
  EXPECT_EQ(DesignValue(f, "kept"), 20U);
  EXPECT_EQ(DesignValue(f, "first"), 1127U);
  EXPECT_EQ(DesignValue(f, "second"), 2071U);
}

void MoveVectors(const svBitVecVal a[2][2][2], svLogicVecVal o[2][2][2]) {
  SeeInC({a[0][1][0], a[1][0][1]});
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 2; ++j) {
      o[i][j][0] = {a[i][j][0], 0};
      o[i][j][1] = {a[i][j][1], a[i][j][1]};
    }
  }
}

TEST(DpiMultidimensionalArrays, AnArrayOfVectorsKeepsItsDimensions) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void move(\n"
      "      input bit [4:0][7:0] a [1:0][3:4],\n"
      "      output logic [39:0] o [1:0][3:4]);\n"
      "  bit [4:0][7:0] a [1:0][3:4];\n"
      "  logic [39:0] o [1:0][3:4];\n"
      "  bit ok_one, ok_two;\n"
      "  initial begin\n"
      "    foreach (a[i, j]) a[i][j] = i * 16 + j;\n"
      "    a[1][3] = 40'h55_0000_0000;\n"
      "    move(a, o);\n"
      "    ok_one = o[0][4] === 40'h00_0000_0004;\n"
      "    ok_two = o[1][3] === {8'b0x0x0x0x, 32'h0};\n"
      "  end\n",
      f, {{"move", CAddress(&MoveVectors)}}, "annex_h_11_02_vectors");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{4, 0x55}));
  EXPECT_EQ(DesignValue(f, "ok_one"), 1U);
  EXPECT_EQ(DesignValue(f, "ok_two"), 1U);
}

void CallExportWithThreeDimensions() {
  auto take =
      NamedExport<void (*)(const int (*)[2][2], int (*)[2])>("take_cube");
  if (take == nullptr) return;
  const int kCube[3][2][2] = {
      {{1, 2}, {3, 4}}, {{5, 6}, {7, 8}}, {{9, 10}, {11, 12}}};
  int out[2][2] = {{0, 0}, {0, 0}};
  take(kCube, out);
  SeeInC({out[0][0], out[0][1], out[1][0], out[1][1]});
}

TEST(DpiMultidimensionalArrays, AnExportTakesMoreThanOneDimension) {
  SimFixture f;
  RunModuleWithC(
      "  export \"DPI-C\" function take_cube;\n"
      "  import \"DPI-C\" context function void call();\n"
      "  int seen;\n"
      "  function void take_cube(input int a [0:2][0:1][0:1],\n"
      "                          output int o [0:1][0:1]);\n"
      "    seen = a[0][1][0] * 100 + a[2][1][0];\n"
      "    foreach (o[i, j]) o[i][j] = i * 10 + j + 1;\n"
      "  endfunction\n"
      "  initial call();\n",
      f, {{"call", CAddress(&CallExportWithThreeDimensions)}},
      "annex_h_11_02_export");
  EXPECT_EQ(DesignValue(f, "seen"), 311U);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 2, 11, 12}));
}

}  // namespace
