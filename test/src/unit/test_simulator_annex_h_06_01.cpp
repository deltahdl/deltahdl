#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

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

}  // namespace
