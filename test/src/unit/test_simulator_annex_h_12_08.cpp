#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

// §H.12.8, the C side of Example 6, compiled against this svdpi.h as the
// example writes it -- under the names this tree's naming rules give C++
// code, F1 for f1: a struct MyType compatible with C, and f1 taking the
// two-dimensional open array by handle, reading the bounds of each of its
// two unpacked dimensions with svLow and svHigh, and visiting every element
// by its own indices through the address svGetArrElemPtr2 computes, reading
// it into a MyType and writing a MyType back.
struct MyType {
  int i;
  int j;
};

// What f1 saw: the bounds it read and the elements it visited.
int g_lo1 = 0;
int g_hi1 = 0;
int g_lo2 = 0;
int g_hi2 = 0;
int g_visited = 0;

void F1(const svOpenArrayHandle h) {
  MyType my_value = {};
  int i = 0;
  int j = 0;
  int lo1 = svLow(h, 1);
  int hi1 = svHigh(h, 1);
  int lo2 = svLow(h, 2);
  int hi2 = svHigh(h, 2);
  g_lo1 = lo1;
  g_hi1 = hi1;
  g_lo2 = lo2;
  g_hi2 = hi2;
  g_visited = 0;

  for (i = lo1; i <= hi1; i++) {
    for (j = lo2; j <= hi2; j++) {
      my_value = *static_cast<MyType*>(svGetArrElemPtr2(h, i, j));
      // Something interesting: the element records the indices it was
      // visited by, so that what f1 wrote back says which element it was.
      my_value.i = i;
      my_value.j = j;
      ++g_visited;
      *static_cast<MyType*>(svGetArrElemPtr2(h, i, j)) = my_value;
    }
  }
}

// An open array of MyType laid out as C lays it out, over the ranges the
// example declares, with room for the larger of its two actuals.
struct OpenArrayOfMyType {
  std::vector<MyType> data;
  SvOpenArrayDimRange ranges[3];
  SvOpenArrayDesc desc;

  OpenArrayOfMyType(int left1, int right1, int left2, int right2)
      : data(static_cast<std::size_t>(Count(left1, right1) *
                                      Count(left2, right2))),
        ranges{{0, 0}, {left1, right1}, {left2, right2}} {
    desc.data = data.data();
    desc.n_dims = 3;
    desc.ranges = ranges;
    desc.elem_size = sizeof(MyType);
  }

  static int Count(int left, int right) {
    return (left > right ? left - right : right - left) + 1;
  }

  svOpenArrayHandle Handle() { return &desc; }
};

// §H.12.8: f1's C prototype takes the open array by handle whatever the
// element type, const svOpenArrayHandle.
TEST(DpiTwoDimensionalOpenArray, TheOpenArrayFormalIsAHandle) {
  DpiArg formal;
  formal.name = "i";
  formal.type = DataTypeKind::kStruct;
  formal.type_name = "MyType";
  formal.direction = Direction::kInput;
  EXPECT_EQ(DpiCTypeOfFormal(formal, true), "const svOpenArrayHandle");
}

// f1(a_10x5): the bounds read are those of [11:20][6:2], every one of the
// 50 elements is visited by its own indices, and the element at [11][6]
// holds what f1 wrote for those indices.
TEST(DpiTwoDimensionalOpenArray, F1VisitsEveryElementOfA10x5ByItsOwnIndices) {
  OpenArrayOfMyType a_10x5(11, 20, 6, 2);
  F1(a_10x5.Handle());
  EXPECT_EQ(g_lo1, 11);
  EXPECT_EQ(g_hi1, 20);
  EXPECT_EQ(g_lo2, 2);
  EXPECT_EQ(g_hi2, 6);
  EXPECT_EQ(g_visited, 50);
  auto* corner = static_cast<MyType*>(svGetArrElemPtr2(a_10x5.Handle(), 11, 6));
  ASSERT_NE(corner, nullptr);
  EXPECT_EQ(corner->i, 11);
  EXPECT_EQ(corner->j, 6);
}

// f1(a_64x8): the same C code over [64:1][-1:-8], 512 elements visited, the
// element at [1][-8] holding what f1 wrote for those indices.
TEST(DpiTwoDimensionalOpenArray, TheSameF1VisitsA64x8OverItsNegativeRange) {
  OpenArrayOfMyType a_64x8(64, 1, -1, -8);
  F1(a_64x8.Handle());
  EXPECT_EQ(g_lo1, 1);
  EXPECT_EQ(g_hi1, 64);
  EXPECT_EQ(g_lo2, -8);
  EXPECT_EQ(g_hi2, -1);
  EXPECT_EQ(g_visited, 512);
  auto* last = static_cast<MyType*>(svGetArrElemPtr2(a_64x8.Handle(), 1, -8));
  ASSERT_NE(last, nullptr);
  EXPECT_EQ(last->i, 1);
  EXPECT_EQ(last->j, -8);
}

}  // namespace
