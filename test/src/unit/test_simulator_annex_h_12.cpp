#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

// Annex H.12 (Open arrays), the clause's own statements before its
// subclauses: a formal declared as an open array takes actuals of different
// sizes, its elements are reached in C by the same range of indices as in
// SystemVerilog, every open array formal is passed by handle whatever its
// direction, and for an inout or output open array the space C code may
// write is determined by the actual's size, writing more than that
// capacity being undefined. The cases check that the element count is the
// actual's and differs from call to call, that the capacity is that count
// of elements in bytes, that a write within the capacity is defined and one
// beyond it is not, and that the handle is the C type of the formal under
// every direction.

namespace {

SvOpenArrayDesc Desc(const SvOpenArrayDimRange* ranges, int n_dims,
                     std::size_t elem_size) {
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = n_dims;
  desc.ranges = ranges;
  desc.elem_size = elem_size;
  return desc;
}

// `bit [7:0] a []` bound to an actual `bit [7:0] x [1:10]`: dimension 0 is
// the packed part, dimension 1 the unpacked one the actual sized.
const SvOpenArrayDimRange kTenOfEight[] = {{7, 0}, {1, 10}};
// `bit [7:0] a [][]` bound to `bit [7:0] y [11:20][6:2]`.
const SvOpenArrayDimRange kFiftyOfEight[] = {{7, 0}, {11, 20}, {6, 2}};
// `bit [] a` bound to `bit [31:0] z`: a packed vector alone.
const SvOpenArrayDimRange kVectorAlone[] = {{31, 0}};
// The same formal `bit [7:0] a []` bound on another call to `bit [7:0] w
// [0:2]`.
const SvOpenArrayDimRange kThreeOfEight[] = {{7, 0}, {0, 2}};

// §H.12: an open array formal takes actuals of different sizes, so the
// count of elements is the actual's on each call -- 10 for x [1:10], 50 for
// y [11:20][6:2], 3 for w [0:2] on a later call of the same formal, and 1
// for a packed vector with no unpacked dimension.
TEST(DpiOpenArrayCapacity, TheActualDeterminesTheElementCount) {
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kTenOfEight, 2, 1)), 10U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kFiftyOfEight, 3, 1)), 50U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kThreeOfEight, 2, 1)), 3U);
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(kVectorAlone, 1, 4)), 1U);
  // A descriptor that records no dimensions describes no actual at all.
  EXPECT_EQ(DpiOpenArrayElementCount(Desc(nullptr, 2, 4)), 0U);
}

// §H.12: for an inout or output open array the space available for C
// output is determined by the actual's size -- the elements it has, each
// the byte stride the handle records: 10 bytes of x, 50 of y, and 48 bytes
// of a 2 by 3 array of svLogicVecVal elements. An element whose
// representation differs from a value's (a stride of 0, §H.12.4) has no
// address to write at and so no capacity.
TEST(DpiOpenArrayCapacity, TheCapacityIsTheActualsSizeInBytes) {
  EXPECT_EQ(DpiOpenArrayCapacityBytes(Desc(kTenOfEight, 2, 1)), 10U);
  EXPECT_EQ(DpiOpenArrayCapacityBytes(Desc(kFiftyOfEight, 3, 1)), 50U);
  const SvOpenArrayDimRange kTwoByThree[] = {{17, 0}, {1, 2}, {0, 2}};
  EXPECT_EQ(
      DpiOpenArrayCapacityBytes(Desc(kTwoByThree, 3, sizeof(SvLogicVecVal))),
      6 * sizeof(SvLogicVecVal));
  EXPECT_EQ(DpiOpenArrayCapacityBytes(Desc(kTenOfEight, 2, 0)), 0U);
}

// §H.12: writing more data to an open array's address than the actual's
// capacity accommodates is undefined -- 10 bytes into x [1:10] of bytes is
// defined, 11 is not, and nothing at all always is.
TEST(DpiOpenArrayCapacity, WritingMoreThanTheCapacityIsUndefined) {
  const SvOpenArrayDesc kTen = Desc(kTenOfEight, 2, 1);
  EXPECT_TRUE(DpiOpenArrayWriteIsDefined(kTen, 10));
  EXPECT_FALSE(DpiOpenArrayWriteIsDefined(kTen, 11));
  EXPECT_TRUE(DpiOpenArrayWriteIsDefined(kTen, 0));
  // The same formal bound to a smaller actual on another call has the
  // smaller capacity: 3 bytes into w [0:2] is defined and 4 is not.
  const SvOpenArrayDesc kThree = Desc(kThreeOfEight, 2, 1);
  EXPECT_TRUE(DpiOpenArrayWriteIsDefined(kThree, 3));
  EXPECT_FALSE(DpiOpenArrayWriteIsDefined(kThree, 4));
}

// §H.12: every formal declared as an open array is passed by handle, of
// type svOpenArrayHandle, regardless of its direction.
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
