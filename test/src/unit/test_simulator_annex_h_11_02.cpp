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

}  // namespace
