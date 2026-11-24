#include <gtest/gtest.h>

#include <cstddef>
#include <string>
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

void AddTenToEach(svOpenArrayHandle h) {
  long long sum = 0;
  int written = 0;
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    auto* element = static_cast<int*>(svGetArrElemPtr1(h, i));
    if (element == nullptr) return;
    sum = (sum * 10) + *element;
    *element += i * 100;
    ++written;
  }
  SeeInC({svSize(h, 1), svLeft(h, 1), svRight(h, 1), sum, written});
}

TEST(DpiOpenArrayCapacity, AnInoutArrayIsIndexedAndWrittenInItsOwnRange) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void add(inout int a []);\n"
      "  int x [3:1];\n"
      "  initial begin\n"
      "    x[3] = 3; x[2] = 2; x[1] = 1;\n"
      "    add(x);\n"
      "  end\n",
      f, {{"add", CAddress(&AddTenToEach)}}, "annex_h_12_inout");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{3, 3, 1, 123, 3}));
  EXPECT_EQ(DesignValue(f, "x[1]"), 101U);
  EXPECT_EQ(DesignValue(f, "x[2]"), 202U);
  EXPECT_EQ(DesignValue(f, "x[3]"), 303U);
}

TEST(DpiOpenArrayCapacity, EachCallGivesTheSizeOfItsOwnActual) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void add(inout int a []);\n"
      "  int x [-2:4];\n"
      "  int y [5:6];\n"
      "  int first;\n"
      "  initial begin\n"
      "    add(x);\n"
      "    add(y);\n"
      "    first = x[-2];\n"
      "  end\n",
      f, {{"add", CAddress(&AddTenToEach)}}, "annex_h_12_two_sizes");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{7, -2, 4, 0, 7, 2, 5, 6, 0, 2}));
  EXPECT_EQ(DesignValue(f, "first"), 0xFFFFFF38U);
  EXPECT_EQ(DesignValue(f, "x[4]"), 400U);
  EXPECT_EQ(DesignValue(f, "y[5]"), 500U);
  EXPECT_EQ(DesignValue(f, "y[6]"), 600U);
}

void FillWithIndices(svOpenArrayHandle h) {
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    auto* element = static_cast<int*>(svGetArrElemPtr1(h, i));
    if (element != nullptr) *element = i + 50;
  }
  SeeInC({svSize(h, 1)});
}

TEST(DpiOpenArrayCapacity, AnOutputArrayIsWrittenToItsLastElement) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void fill(output int a []);\n"
      "  int x [10:4];\n"
      "  initial fill(x);\n",
      f, {{"fill", CAddress(&FillWithIndices)}}, "annex_h_12_output");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{7}));
  EXPECT_EQ(DesignValue(f, "x[10]"), 60U);
  EXPECT_EQ(DesignValue(f, "x[4]"), 54U);
}

}  // namespace
