#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(DpiActualRanges, SizedAndOpenFormalsTradePerformanceForConvenience) {
  EXPECT_TRUE(DpiProgrammerChoosesFormalSizing());
  EXPECT_EQ(DpiPassingModeOfSizing(DpiFormalArraySizing::kSized),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfSizing(DpiFormalArraySizing::kOpen),
            DpiPassingMode::kByHandle);
  EXPECT_FALSE(DpiSizingHasOverhead(DpiFormalArraySizing::kSized));
  EXPECT_TRUE(DpiSizingHasOverhead(DpiFormalArraySizing::kOpen));
  EXPECT_EQ(DpiAccessibilityOfSizing(DpiFormalArraySizing::kSized),
            DpiArrayAccessibility::kDirectlyAsNormalizedArray);
  EXPECT_EQ(DpiAccessibilityOfSizing(DpiFormalArraySizing::kOpen),
            DpiArrayAccessibility::kMostlyIndirectlyThroughTheHandle);
}

std::vector<SvActualDimension> PackedOfA() { return {{15, 0}}; }
std::vector<SvActualDimension> UnpackedOfA() { return {{63, 0}, {7, 0}}; }
std::vector<SvActualDimension> PackedOfB() { return {{31, 16}}; }
std::vector<SvActualDimension> UnpackedOfB() { return {{64, 1}, {-1, -8}}; }

DpiFormalDimension Unsized() { return DpiFormalDimension{false, {0, 0}}; }

DpiFormalDimension Sized(SvActualDimension range) {
  return DpiFormalDimension{true, range};
}

void ExpectRange(const SvActualDimension& range, int32_t left, int32_t right) {
  EXPECT_EQ(range.low, left);
  EXPECT_EQ(range.high, right);
}

TEST(DpiActualRanges, AnOpenFormalKeepsTheActualsUnpackedRanges) {
  const std::vector<SvActualDimension> kRanges = DpiCRangesAtCall(
      Unsized(), {Unsized(), Unsized()}, PackedOfB(), UnpackedOfB());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 64, 1);
  ExpectRange(kRanges[2], -1, -8);
}

TEST(DpiActualRanges, AnOpenFormalsRangesAreTheActualsPerCall) {
  const std::vector<SvActualDimension> kRanges = DpiCRangesAtCall(
      Unsized(), {Unsized(), Unsized()}, PackedOfA(), UnpackedOfA());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 63, 0);
  ExpectRange(kRanges[2], 7, 0);
}

TEST(DpiActualRanges, ASizedFormalIsNormalizedThroughout) {
  const std::vector<SvActualDimension> kRanges =
      DpiCRangesAtCall(Sized({31, 16}), {Sized({64, 1}), Sized({-1, -8})},
                       PackedOfB(), UnpackedOfB());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 0, 63);
  ExpectRange(kRanges[2], 0, 7);
}

TEST(DpiActualRanges, TheActualsIndicesMapOntoTheNormalizedOnes) {
  std::vector<uint32_t> first =
      DpiCIndicesOfUnpackedElement(UnpackedOfB(), {64, -1});
  ASSERT_EQ(first.size(), 2u);
  EXPECT_EQ(first[0], 63u);
  EXPECT_EQ(first[1], 7u);
  std::vector<uint32_t> last =
      DpiCIndicesOfUnpackedElement(UnpackedOfB(), {1, -8});
  EXPECT_EQ(last[0], 0u);
  EXPECT_EQ(last[1], 0u);
  std::vector<uint32_t> tip =
      DpiCIndicesOfUnpackedElement({{0, 63}, {0, 7}}, {5, 3});
  EXPECT_EQ(tip[0], 5u);
  EXPECT_EQ(tip[1], 3u);
}

void SeeRangesAndAnElement(svOpenArrayHandle i) {
  svLogicVecVal element = {0, 0};
  svGetLogicArrElem2VecVal(&element, i, svLeft(i, 1), svRight(i, 2));
  SeeInC({svLeft(i, 0), svRight(i, 0), svLeft(i, 1), svRight(i, 1),
          svLeft(i, 2), svRight(i, 2), element.aval & 0xFFFF,
          element.bval & 0xFFFF});
}

void SeeNormalizedElements(const svLogicVecVal (*i)[8]) {
  SeeInC({i[0][0].aval & 0xFFFF, i[63][7].aval & 0xFFFF, i[63][0].aval & 0xFFFF,
          i[1][2].aval & 0xFFFF});
}

void RunTheSizedAndOpenPair(SimFixture& f, const char* call,
                            const char* dir_name) {
  RunModuleWithC(
      std::string(
          "  logic [15:0] a_64x8 [63:0][7:0];\n"
          "  logic [31:16] b_64x8 [64:1][-1:-8];\n"
          "  import \"DPI-C\" function void f1(input logic [] i [][]);\n"
          "  import \"DPI-C\" function void f2(\n"
          "      input logic [31:16] i [64:1][-1:-8]);\n"
          "  initial begin\n"
          "    foreach (a_64x8[j, k]) a_64x8[j][k] = 16'h4000 + j * 16 + k;\n"
          "    foreach (b_64x8[j, k]) b_64x8[j][k] = 16'h8000 + j * 16 - k;\n"
          "    a_64x8[63][0] = 16'bx000_0000_0000_01z1;\n") +
          "    " + call + ";\n  end\n",
      f,
      {{"f1", CAddress(&SeeRangesAndAnElement)},
       {"f2", CAddress(&SeeNormalizedElements)}},
      dir_name);
}

TEST(DpiActualRanges, DISABLED_AnOpenFormalSeesTheRangesOfA) {
  SimFixture f;
  RunTheSizedAndOpenPair(f, "f1(a_64x8)", "annex_h_12_01_a");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{15, 0, 63, 0, 7, 0, 0x8005, 0x8002}));
}

TEST(DpiActualRanges, DISABLED_AnOpenFormalSeesTheRangesOfB) {
  SimFixture f;
  RunTheSizedAndOpenPair(f, "f1(b_64x8)", "annex_h_12_01_b");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{15, 0, 64, 1, -1, -8, 0x8408, 0}));
}

TEST(DpiActualRanges, ASizedFormalSeesNormalizedRangesOfB) {
  SimFixture f;
  RunTheSizedAndOpenPair(f, "f2(b_64x8)", "annex_h_12_01_sized");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{0x8018, 0x8401, 0x8408, 0x8026}));
}

void SelectFromLogicElements(svOpenArrayHandle h) {
  SeeInC({svLeft(h, 0), svRight(h, 0), svLow(h, 1), svHigh(h, 1)});
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    svLogicVecVal element = {0, 0};
    svLogicVecVal part = {0, 0};
    svGetLogicArrElem1VecVal(&element, h, i);
    svGetPartselLogic(&part, &element, 4, 8);
    SeeInC({svGetBitselLogic(&element, 15)});
    SeeInC({svGetBitselLogic(&element, 0)});
    SeeInC({part.aval});
    SeeInC({part.bval});
  }
}

void SelectFromBitElements(svOpenArrayHandle h) {
  SeeInC({svLeft(h, 0), svRight(h, 0), svLow(h, 1), svHigh(h, 1)});
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    svBitVecVal element = 0;
    svBitVecVal part = 0;
    svGetBitArrElem1VecVal(&element, h, i);
    svGetPartselBit(&part, &element, 4, 8);
    SeeInC({svGetBitselBit(&element, 15)});
    SeeInC({svGetBitselBit(&element, 0)});
    SeeInC({part});
  }
}

TEST(DpiActualRanges, DISABLED_SelectsOfALogicElementUseItsNormalizedRange) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input logic [] i []);\n"
      "  logic [31:16] v [6:5];\n"
      "  initial begin\n"
      "    v[5] = 16'b1011_0x1z_1100_0110;\n"
      "    v[6] = 16'bz000_1010_0101_111x;\n"
      "    see(v);\n"
      "  end\n",
      f, {{"see", CAddress(&SelectFromLogicElements)}}, "annex_h_12_01_logic");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{15, 0, 5, 6, sv_1, sv_0, 0x6C,
                                               0x50, sv_z, sv_x, 0xA5, 0}));
}

TEST(DpiActualRanges, DISABLED_SelectsOfABitElementUseItsNormalizedRange) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input bit [] i []);\n"
      "  bit [31:16] v [6:5];\n"
      "  initial begin\n"
      "    v[5] = 16'h9a52;\n"
      "    v[6] = 16'h1ce1;\n"
      "    see(v);\n"
      "  end\n",
      f, {{"see", CAddress(&SelectFromBitElements)}}, "annex_h_12_01_bit");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{15, 0, 5, 6, 1, 0, 0xA5, 0, 1, 0xCE}));
}

}  // namespace
