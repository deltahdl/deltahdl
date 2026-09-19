#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

// §H.11.2: multiple packed dimensions are linearized into one normalized
// packed dimension -- `bit [6:1][1:8]` is [47:0], three dimensions [1:0]
// [3:0][7:0] are [63:0], and one dimension [29:0] is its own normalization.
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

// §H.11.2 with §H.7.7: the linearized dimension is what the canonical
// representation holds, one chunk per 32 bits of it -- two for the 48 bits
// of `bit [6:1][1:8]`, and the C declaration of `bit [6:1][1:8] b [65:2]`
// carries that one chunk dimension after the unpacked one.
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

// §H.11.2: unpacked arrays can have an arbitrary number of dimensions --
// four here, each a dimension of the C array, and an element reached by its
// four indices counted from the low bounds.
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

// §H.11.2 with §H.12.2: an open array's handle reports as many unpacked
// dimensions as the actual has -- four, at dimensions 1 to 4 -- beside its
// one packed dimension at 0, five in all as $dimensions of §20.7 counts.
TEST(DpiMultidimensionalArrays, AnOpenArrayReportsEveryUnpackedDimension) {
  const SvOpenArrayDimRange kRanges[] = {
      {47, 0}, {1, 0}, {2, 0}, {3, 0}, {1, 4}};
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = 5;
  desc.ranges = kRanges;
  desc.elem_size = 0;
  svOpenArrayHandle h = &desc;
  EXPECT_EQ(svDimensions(h), 5);
  EXPECT_EQ(svSize(h, 0), 48);
  EXPECT_EQ(svSize(h, 4), 4);
}

}  // namespace
