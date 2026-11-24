#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

DpiFormalDimension Sized(int32_t left, int32_t right) {
  return DpiFormalDimension{true, SvActualDimension{left, right}};
}

DpiFormalDimension Unsized() { return DpiFormalDimension{false, {}}; }

bool SameRanges(const std::vector<SvActualDimension>& got,
                const std::vector<SvActualDimension>& want) {
  if (got.size() != want.size()) return false;
  for (std::size_t k = 0; k < got.size(); ++k) {
    if (got[k].low != want[k].low || got[k].high != want[k].high) return false;
  }
  return true;
}

TEST(DpiFormalTypes, ASizedFormalIsFullyDefinedByTheDeclaration) {
  const std::vector<SvActualDimension> kRanges =
      DpiFormalRangesAtCall(Sized(7, 0), {Sized(1, 4)}, {{15, 0}}, {{0, 9}});
  EXPECT_TRUE(SameRanges(kRanges, {{7, 0}, {1, 4}}));
}

TEST(DpiFormalTypes, AnOpenArraysUnpackedDimensionsMatchTheActuals) {
  EXPECT_TRUE(SameRanges(
      DpiFormalRangesAtCall(Sized(15, 8), {Unsized()}, {{15, 8}}, {{3, 1}}),
      {{15, 8}, {3, 1}}));
  EXPECT_TRUE(SameRanges(
      DpiFormalRangesAtCall(Sized(15, 8), {Unsized()}, {{15, 8}}, {{0, 9}}),
      {{15, 8}, {0, 9}}));
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Sized(15, 8), {Unsized(), Unsized()},
                                       {{15, 8}}, {{11, 20}, {6, 2}}),
                 {{15, 8}, {11, 20}, {6, 2}}));
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Sized(15, 8), {Sized(0, 1), Unsized()},
                                       {{15, 8}}, {{5, 6}, {6, 2}}),
                 {{15, 8}, {0, 1}, {6, 2}}));
}

TEST(DpiFormalTypes, AnOpenArraysPackedDimensionIsLinearizedAndNormalized) {
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Unsized(), {Unsized()},
                                       {{2, 3}, {1, 3}, {2, 0}}, {{1, 10}}),
                 {{17, 0}, {1, 10}}));
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Unsized(), {}, {{7, 4}}, {}), {{3, 0}}));
}

std::vector<int>& RecordedRanges() {
  static std::vector<int> ranges;
  return ranges;
}

void RecordDimension(svOpenArrayHandle h, int d) {
  RecordedRanges().push_back(svLeft(h, d));
  RecordedRanges().push_back(svRight(h, d));
}

void RecordPackedPart(svOpenArrayHandle h) {
  RecordDimension(h, 0);
  RecordedRanges().push_back(svSize(h, 0));
}

void RecordUnpackedPart(svOpenArrayHandle h) {
  RecordDimension(h, 1);
  RecordedRanges().push_back(svSize(h, 1));
}

void RecordBothParts(svOpenArrayHandle h) {
  RecordDimension(h, 0);
  RecordDimension(h, 1);
  RecordDimension(h, 2);
}

void FillByIndex(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    const svBitVecVal kValue = 0x50U + static_cast<uint32_t>(i);
    svPutBitArrElem1VecVal(h, &kValue, i);
  }
}

int WeightedByPosition(const svBitVecVal* a) {
  return static_cast<int>((a[0] & 255U) + ((a[1] & 255U) * 10) +
                          ((a[2] & 255U) * 100) + ((a[3] & 255U) * 1000));
}

void FillThree(int* o) {
  o[0] = 9;
  o[1] = 8;
  o[2] = 7;
}

void RunFormalTypes(const std::string& items, SimFixture& f) {
  RecordedRanges().clear();
  RunWithImportsBound(
      "module t;\n" + items + "endmodule\n", f,
      {{"packed_part", reinterpret_cast<void*>(&RecordPackedPart)},
       {"unpacked_part", reinterpret_cast<void*>(&RecordUnpackedPart)},
       {"both_parts", reinterpret_cast<void*>(&RecordBothParts)},
       {"fill_by_index", reinterpret_cast<void*>(&FillByIndex)},
       {"weighted", reinterpret_cast<void*>(&WeightedByPosition)},
       {"fill_three", reinterpret_cast<void*>(&FillThree)}},
      "annex_h_06_01_formal_types");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(DpiFormalTypesInADesign, EachCallsActualGivesAnOpenArrayItsRange) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void unpacked_part(input int a []);\n"
      "  int u [5:2];\n"
      "  int w [-1:1];\n"
      "  initial begin unpacked_part(u); unpacked_part(w); end\n",
      f);
  EXPECT_EQ(RecordedRanges(), (std::vector<int>{5, 2, 4, -1, 1, 3}));
}

TEST(DpiFormalTypesInADesign, DISABLED_AnUnsizedPackedPartIsLinearized) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void packed_part(input bit [] a);\n"
      "  bit [3:0][7:0] x;\n"
      "  bit [7:4] y;\n"
      "  initial begin packed_part(x); packed_part(y); end\n",
      f);
  EXPECT_EQ(RecordedRanges(), (std::vector<int>{31, 0, 32, 3, 0, 4}));
}

TEST(DpiFormalTypesInADesign,
     DISABLED_AnUnsizedFourStatePackedPartIsLinearized) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void packed_part(input logic [] a);\n"
      "  logic [2:1][1:0] x;\n"
      "  initial packed_part(x);\n",
      f);
  EXPECT_EQ(RecordedRanges(), (std::vector<int>{3, 0, 4}));
}

TEST(DpiFormalTypesInADesign,
     DISABLED_AnUnsizedPackedPartIsNormalizedUnderAnArray) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void both_parts(input logic [] i [][]);\n"
      "  logic [31:16] b_64x8 [64:1][-1:-8];\n"
      "  initial both_parts(b_64x8);\n",
      f);
  EXPECT_EQ(RecordedRanges(), (std::vector<int>{15, 0, 64, 1, -1, -8}));
}

TEST(DpiFormalTypesInADesign,
     DISABLED_BothPartsOfAnActualMayBeMultidimensional) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void both_parts(input bit [] a [][]);\n"
      "  bit [1:0][3:0] x [2:0][1:0];\n"
      "  initial both_parts(x);\n",
      f);
  EXPECT_EQ(RecordedRanges(), (std::vector<int>{7, 0, 2, 0, 1, 0}));
}

TEST(DpiFormalTypesInADesign,
     DISABLED_AnOpenPackedOutputIsWrittenBackBitForBit) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void fill_by_index(output bit [] a []);\n"
      "  bit [1:0][3:0] x [2:0];\n"
      "  initial fill_by_index(x);\n",
      f);
  EXPECT_EQ(DesignValue(f, "x[0]"), 0x50U);
  EXPECT_EQ(DesignValue(f, "x[2]"), 0x52U);
}

TEST(DpiFormalTypesInADesign, ASizedFormalKeepsItsDeclaredLayout) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function int weighted(input bit [7:0] a [1:4]);\n"
      "  bit [7:0] x [5:8] = '{1, 2, 3, 4};\n"
      "  bit [8:1] y [0:3] = '{5, 6, 7, 8};\n"
      "  int r, q;\n"
      "  initial begin r = weighted(x); q = weighted(y); end\n",
      f);
  EXPECT_EQ(DesignValue(f, "r"), 4321U);
  EXPECT_EQ(DesignValue(f, "q"), 8765U);
}

TEST(DpiFormalTypesInADesign, DISABLED_ADescendingActualMatchesLeftToRight) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function int weighted(input bit [7:0] a [0:3]);\n"
      "  bit [7:0] r [3:0] = '{4, 3, 2, 1};\n"
      "  int w;\n"
      "  initial w = weighted(r);\n",
      f);
  EXPECT_EQ(DesignValue(f, "w"), 1234U);
}

TEST(DpiFormalTypesInADesign, DISABLED_ADescendingFormalMatchesLeftToRight) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function int weighted(input bit [7:0] a [4:1]);\n"
      "  bit [7:0] x [0:3] = '{1, 2, 3, 4};\n"
      "  int w;\n"
      "  initial w = weighted(x);\n",
      f);
  EXPECT_EQ(DesignValue(f, "w"), 1234U);
}

TEST(DpiFormalTypesInADesign,
     DISABLED_ADescendingOutputFormalMatchesLeftToRight) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void fill_three(output int o [3:1]);\n"
      "  int p [0:2];\n"
      "  initial fill_three(p);\n",
      f);
  EXPECT_EQ(DesignValue(f, "p[0]"), 7U);
  EXPECT_EQ(DesignValue(f, "p[1]"), 8U);
  EXPECT_EQ(DesignValue(f, "p[2]"), 9U);
}

TEST(DpiFormalTypesInADesign, ASizedOutputFormalKeepsItsDeclaredLayout) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void fill_three(output int o [1:3]);\n"
      "  int p [5:7];\n"
      "  initial fill_three(p);\n",
      f);
  EXPECT_EQ(DesignValue(f, "p[5]"), 9U);
  EXPECT_EQ(DesignValue(f, "p[6]"), 8U);
  EXPECT_EQ(DesignValue(f, "p[7]"), 7U);
}

TEST(DpiFormalTypesInADesign,
     DISABLED_AnAscendingOutputFillsADescendingActual) {
  SimFixture f;
  RunFormalTypes(
      "  import \"DPI-C\" function void fill_three(output int o [0:2]);\n"
      "  int p [2:0];\n"
      "  initial fill_three(p);\n",
      f);
  EXPECT_EQ(DesignValue(f, "p[2]"), 9U);
  EXPECT_EQ(DesignValue(f, "p[1]"), 8U);
  EXPECT_EQ(DesignValue(f, "p[0]"), 7U);
}

}  // namespace
