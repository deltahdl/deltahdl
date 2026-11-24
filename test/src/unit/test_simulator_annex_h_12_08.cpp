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

struct MyType {
  int i;
  int j;
};

int g_lo1 = 0;
int g_hi1 = 0;
int g_lo2 = 0;
int g_hi2 = 0;
int g_visited = 0;

void F1(svOpenArrayHandle h) {
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
      my_value.i = i;
      my_value.j = j;
      ++g_visited;
      *static_cast<MyType*>(svGetArrElemPtr2(h, i, j)) = my_value;
    }
  }
}

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
    desc.has_packed_part = 0;
    desc.ranges = ranges;
    desc.elem_size = sizeof(MyType);
  }

  static int Count(int left, int right) {
    return (left > right ? left - right : right - left) + 1;
  }

  svOpenArrayHandle Handle() { return &desc; }
};

TEST(DpiTwoDimensionalOpenArray, TheOpenArrayFormalIsAHandle) {
  DpiArg formal;
  formal.name = "i";
  formal.type = DataTypeKind::kStruct;
  formal.type_name = "MyType";
  formal.direction = Direction::kInput;
  EXPECT_EQ(DpiCTypeOfFormal(formal, true), "const svOpenArrayHandle");
}

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

void SeeEveryElement(svOpenArrayHandle h) {
  long long sum = 0;
  int visited = 0;
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    for (int j = svLow(h, 2); j <= svHigh(h, 2); ++j) {
      const auto* element =
          static_cast<const MyType*>(svGetArrElemPtr2(h, i, j));
      if (element == nullptr) return;
      sum += static_cast<long long>(element->i) * element->j;
      ++visited;
    }
  }
  SeeInC({svLow(h, 1), svHigh(h, 1), svLow(h, 2), svHigh(h, 2), visited, sum});
}

void RunTwoDimensionalExample(SimFixture& f, const char* call,
                              const char* dir_name) {
  RunModuleWithC(
      std::string("  typedef struct { int i; int j; } MyType;\n"
                  "  import \"DPI-C\" function void f1(input MyType i [][]);\n"
                  "  MyType a_10x5 [11:20][6:2];\n"
                  "  MyType a_64x8 [64:1][-1:-8];\n"
                  "  initial begin\n"
                  "    foreach (a_10x5[x, y]) begin\n"
                  "      a_10x5[x][y].i = x; a_10x5[x][y].j = y;\n"
                  "    end\n"
                  "    foreach (a_64x8[x, y]) begin\n"
                  "      a_64x8[x][y].i = x; a_64x8[x][y].j = y;\n"
                  "    end\n") +
          "    " + call + ";\n  end\n",
      f, {{"f1", CAddress(&SeeEveryElement)}}, dir_name);
}

TEST(DpiTwoDimensionalOpenArray, ADesignsA10x5IsVisitedByItsOwnIndices) {
  SimFixture f;
  RunTwoDimensionalExample(f, "f1(a_10x5)", "annex_h_12_08_a");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{11, 20, 2, 6, 50, 155LL * 20}));
}

TEST(DpiTwoDimensionalOpenArray, ADesignsA64x8IsVisitedByItsOwnIndices) {
  SimFixture f;
  RunTwoDimensionalExample(f, "f1(a_64x8)", "annex_h_12_08_b");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{1, 64, -8, -1, 512, 2080LL * -36}));
}

}  // namespace
