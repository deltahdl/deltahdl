#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

SvOpenArrayDesc Desc(const SvOpenArrayDimRange* ranges, int n_dims,
                     std::size_t elem_size) {
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = n_dims;
  desc.has_packed_part = 1;
  desc.ranges = ranges;
  desc.elem_size = elem_size;
  return desc;
}

const SvOpenArrayDimRange kTenOfEight[] = {{7, 0}, {1, 10}};
const SvOpenArrayDimRange kFiftyOfEight[] = {{7, 0}, {11, 20}, {6, 2}};
const SvOpenArrayDimRange kVectorAlone[] = {{31, 0}};
const SvOpenArrayDimRange kThreeOfEight[] = {{7, 0}, {0, 2}};

TEST(DpiOpenArrayCapacity, TheActualDeterminesTheElementCount) {
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kTenOfEight, 2, 1)), 10U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kFiftyOfEight, 3, 1)), 50U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kThreeOfEight, 2, 1)), 3U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kVectorAlone, 1, 4)), 1U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(nullptr, 2, 4)), 0U);
}

TEST(DpiOpenArrayCapacity, TheCapacityIsTheActualsSizeInBytes) {
  EXPECT_EQ(DpiOpenArrayCapacityBytes(Desc(kTenOfEight, 2, 1)), 10U);
  EXPECT_EQ(DpiOpenArrayCapacityBytes(Desc(kFiftyOfEight, 3, 1)), 50U);
  const SvOpenArrayDimRange kTwoByThree[] = {{17, 0}, {1, 2}, {0, 2}};
  EXPECT_EQ(
      DpiOpenArrayCapacityBytes(Desc(kTwoByThree, 3, sizeof(SvLogicVecVal))),
      6 * sizeof(SvLogicVecVal));
  EXPECT_EQ(DpiOpenArrayCapacityBytes(Desc(kTenOfEight, 2, 0)), 0U);
}

TEST(DpiOpenArrayCapacity, WritingMoreThanTheCapacityIsUndefined) {
  const SvOpenArrayDesc kTen = Desc(kTenOfEight, 2, 1);
  EXPECT_TRUE(DpiOpenArrayWriteIsDefined(kTen, 10));
  EXPECT_FALSE(DpiOpenArrayWriteIsDefined(kTen, 11));
  EXPECT_TRUE(DpiOpenArrayWriteIsDefined(kTen, 0));
  const SvOpenArrayDesc kThree = Desc(kThreeOfEight, 2, 1);
  EXPECT_TRUE(DpiOpenArrayWriteIsDefined(kThree, 3));
  EXPECT_FALSE(DpiOpenArrayWriteIsDefined(kThree, 4));
}

TEST(DpiOpenArrayCapacity, AnOpenArrayFormalIsAHandleUnderEveryDirection) {
  DpiArg formal;
  formal.name = "a";
  formal.type = DataTypeKind::kBit;
  formal.width = 8;
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    formal.direction = kDirection;
    EXPECT_EQ(DpiCTypeOfFormal(formal, true), "const svOpenArrayHandle");
  }
}

}  // namespace
