#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.6.1 (Types of formal arguments): the WYSIWYG principle has an
// actual be of the type the import declaration specifies for the formal,
// open arrays excepted, so a formal other than an open array is fully
// defined by the declaration, its packed and unpacked ranges exactly as
// written there, the declaration site alone being relevant; an open array
// formal's unpacked dimensions match the actual's, its packed dimension is
// the linearized, normalized version of all the actual's packed
// dimensions, and its unsized ranges are determined at each call site
// while the rest of its type is specified at the declaration -- so `bit
// [15:8] b []` is an unpacked array of packed bit arrays with bounds 15 to
// 8 whose unpacked bounds each call's actual defines. The cases check the
// ranges a formal has on a call under each of those rules.

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

// §H.6.1: a formal other than an open array is fully defined by the import
// declaration -- `bit [7:0] a [1:4]` has those ranges on every call, the
// actual's own [15:0] and [0:9] being no part of the formal's type.
TEST(DpiFormalTypes, ASizedFormalIsFullyDefinedByTheDeclaration) {
  const std::vector<SvActualDimension> kRanges =
      DpiFormalRangesAtCall(Sized(7, 0), {Sized(1, 4)}, {{15, 0}}, {{0, 9}});
  EXPECT_TRUE(SameRanges(kRanges, {{7, 0}, {1, 4}}));
}

// §H.6.1: an open array formal's unpacked dimensions match the actual's,
// and are determined at each call -- `bit [15:8] b []` keeps its packed
// bounds 15 to 8 from the declaration and takes [3:1] from one call's
// actual and [0:9] from another's, and `bit [15:8] c [][]` takes both of
// [11:20][6:2].
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
  // A sized unpacked dimension beside an unsized one keeps the
  // declaration's range where the unsized takes the actual's.
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Sized(15, 8), {Sized(0, 1), Unsized()},
                                       {{15, 8}}, {{5, 6}, {6, 2}}),
                 {{15, 8}, {0, 1}, {6, 2}}));
}

// §H.6.1: an open array's unsized packed dimension is the linearized,
// normalized version of all the actual's packed dimensions -- `bit [] d []`
// bound to `bit [2:3][1:3][2:0] x [1:10]` has 18 bits, [17:0], and the
// actual's [1:10] -- and `logic [] e` bound to `logic [7:4] y` is [3:0].
TEST(DpiFormalTypes, AnOpenArraysPackedDimensionIsLinearizedAndNormalized) {
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Unsized(), {Unsized()},
                                       {{2, 3}, {1, 3}, {2, 0}}, {{1, 10}}),
                 {{17, 0}, {1, 10}}));
  EXPECT_TRUE(
      SameRanges(DpiFormalRangesAtCall(Unsized(), {}, {{7, 4}}, {}), {{3, 0}}));
}

}  // namespace
