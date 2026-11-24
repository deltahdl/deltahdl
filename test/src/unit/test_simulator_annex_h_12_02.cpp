#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <type_traits>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

namespace {

svOpenArrayHandle MakeHandle(const SvOpenArrayDimRange* ranges, int n_dims,
                             SvOpenArrayDesc* desc) {
  desc->data = nullptr;
  desc->n_dims = n_dims;
  desc->has_packed_part = 1;
  desc->ranges = ranges;
  return desc;
}

TEST(ArrayQueryingFunctions, DimensionZeroIsPackedPart) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {0, 7}, {-1, -8}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 3, &desc);

  EXPECT_EQ(svLeft(h, 0), 15);
  EXPECT_EQ(svRight(h, 0), 0);

  EXPECT_EQ(svLeft(h, 1), 0);
  EXPECT_EQ(svRight(h, 1), 7);
  EXPECT_EQ(svLeft(h, 2), -1);
  EXPECT_EQ(svRight(h, 2), -8);
}

TEST(ArrayQueryingFunctions, LowHighSizeAnswerForAnAscendingRange) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {0, 7}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLow(h, 1), 0);
  EXPECT_EQ(svHigh(h, 1), 7);
  EXPECT_EQ(svSize(h, 1), 8);
}

TEST(ArrayQueryingFunctions, LowHighSizeAnswerForADescendingRange) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {-1, -8}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLow(h, 0), 0);
  EXPECT_EQ(svHigh(h, 0), 15);
  EXPECT_EQ(svSize(h, 0), 16);

  EXPECT_EQ(svLow(h, 1), -8);
  EXPECT_EQ(svHigh(h, 1), -1);
  EXPECT_EQ(svSize(h, 1), 8);
}

TEST(ArrayQueryingFunctions, IncrementAnswersForBothDirections) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {0, 7}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svIncrement(h, 0), 1);
  EXPECT_EQ(svIncrement(h, 1), -1);
}

TEST(ArrayQueryingFunctions, DimensionsCountsPackedPlusUnpacked) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {0, 7}, {-1, -8}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 3, &desc);

  EXPECT_EQ(svDimensions(h), 3);
}

TEST(ArrayQueryingFunctions, DegenerateSingleElementRange) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLow(h, 0), 0);
  EXPECT_EQ(svHigh(h, 0), 0);
  EXPECT_EQ(svSize(h, 0), 1);
  EXPECT_EQ(svIncrement(h, 0), 1);
}

TEST(ArrayQueryingFunctions, OutOfRangeDimensionAndNullHandle) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {0, 7}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLeft(h, 2), 0);
  EXPECT_EQ(svRight(h, 5), 0);
  EXPECT_EQ(svLow(h, -1), 0);
  EXPECT_EQ(svHigh(h, 2), 0);
  EXPECT_EQ(svSize(h, 2), 0);
  EXPECT_EQ(svIncrement(h, 2), 0);

  EXPECT_EQ(svDimensions(nullptr), 0);
  EXPECT_EQ(svLeft(nullptr, 0), 0);
  EXPECT_EQ(svSize(nullptr, 0), 0);
  EXPECT_EQ(svIncrement(nullptr, 0), 0);
  EXPECT_EQ(svGetArrElemPtr(nullptr, 0), nullptr);
}

struct Pair {
  int i;
  int j;
};

int DimensionsOfPairs(svOpenArrayHandle h) {
  int sum = 0;
  for (int a = svLow(h, 1); a <= svHigh(h, 1); ++a) {
    for (int b = svLow(h, 2); b <= svHigh(h, 2); ++b) {
      sum += static_cast<Pair*>(svGetArrElemPtr(h, a, b))->i;
    }
  }
  return (svDimensions(h) * 1000) + sum;
}

int DimensionsOfReals(svOpenArrayHandle h) {
  return (svDimensions(h) * 10) + svSize(h, 1);
}

int DimensionsOfInts(svOpenArrayHandle h) {
  return (svDimensions(h) * 100) + svLeft(h, 0);
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(ArrayQueryingFunctions, AnElementWithNoPackedPartAddsNoDimension) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  typedef struct { int i; int j; } pair;\n"
      "  import \"DPI-C\" function int dims_of_pairs(input pair a [][]);\n"
      "  import \"DPI-C\" function int dims_of_reals(input real a []);\n"
      "  import \"DPI-C\" function int dims_of_ints(input int a []);\n"
      "  pair pa [11:12][6:8];\n"
      "  real ra [1:3];\n"
      "  int ia [2:5];\n"
      "  int s1, s2, s3;\n"
      "  initial begin\n"
      "    foreach (pa[x, y]) pa[x][y].i = x + y;\n"
      "    s1 = dims_of_pairs(pa);\n"
      "    s2 = dims_of_reals(ra);\n"
      "    s3 = dims_of_ints(ia);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"dims_of_pairs", reinterpret_cast<void*>(&DimensionsOfPairs)},
       {"dims_of_reals", reinterpret_cast<void*>(&DimensionsOfReals)},
       {"dims_of_ints", reinterpret_cast<void*>(&DimensionsOfInts)}},
      "annex_h_12_02_dimensions");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "s1"), 2111U);
  EXPECT_EQ(VariableValue(f, "s2"), 13U);
  EXPECT_EQ(VariableValue(f, "s3"), 231U);
}

void SeeQueries(svOpenArrayHandle h) {
  SeeInC({svDimensions(h)});
  for (int d = 1; d <= svDimensions(h) && d <= 2; ++d) {
    for (long long answer : {svLeft(h, d), svRight(h, d), svLow(h, d),
                             svHigh(h, d), svIncrement(h, d), svSize(h, d)}) {
      SeeInC({answer});
    }
  }
}

TEST(ArrayQueryingFunctions, EachFunctionAnswersForAnArrayOfReals) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input real a []);\n"
      "  real a [4:-1];\n"
      "  initial see(a);\n",
      f, {{"see", CAddress(&SeeQueries)}}, "annex_h_12_02_reals");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 4, -1, -1, 4, 1, 6}));
}

TEST(ArrayQueryingFunctions, EachFunctionAnswersForTwoDimensions) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input int a [][]);\n"
      "  int a [7:3][-5:2];\n"
      "  initial see(a);\n",
      f, {{"see", CAddress(&SeeQueries)}}, "annex_h_12_02_two");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{3, 7, 3, 3, 7, 1, 5, -5, 2, -5, 2, -1, 8}));
}

void SeePackedQueries(svOpenArrayHandle h) {
  SeeInC({svDimensions(h), svLeft(h, 0), svRight(h, 0), svLow(h, 0),
          svHigh(h, 0), svIncrement(h, 0), svSize(h, 0)});
}

void RunPackedQueries(SimFixture& f, const char* declaration,
                      const char* dir_name) {
  RunModuleWithC(std::string("  import \"DPI-C\" function void see(") +
                     "input bit [] a);\n" + "  " + declaration +
                     ";\n  initial see(v);\n",
                 f, {{"see", CAddress(&SeePackedQueries)}}, dir_name);
}

TEST(ArrayQueryingFunctions,
     DISABLED_EachFunctionAnswersForAnUnsizedPackedFormal) {
  SimFixture f;
  RunPackedQueries(f, "bit [3:0][7:0] v", "annex_h_12_02_packed");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 31, 0, 0, 31, 1, 32}));
}

TEST(ArrayQueryingFunctions,
     DISABLED_AnUnsizedPackedFormalNormalizesItsActual) {
  SimFixture f;
  RunPackedQueries(f, "bit [2:1][4:8] v", "annex_h_12_02_offset");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 9, 0, 0, 9, 1, 10}));
}

TEST(ArrayQueryingFunctions, TheQueriesHaveTheirPrototypes) {
  EXPECT_TRUE((std::is_same_v<decltype(svLeft), int(svOpenArrayHandle, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svRight), decltype(svLeft)>));
  EXPECT_TRUE((std::is_same_v<decltype(svLow), decltype(svLeft)>));
  EXPECT_TRUE((std::is_same_v<decltype(svHigh), decltype(svLeft)>));
  EXPECT_TRUE((std::is_same_v<decltype(svIncrement), decltype(svLeft)>));
  EXPECT_TRUE((std::is_same_v<decltype(svSize), decltype(svLeft)>));
  EXPECT_TRUE((std::is_same_v<decltype(svDimensions), int(svOpenArrayHandle)>));
}

}  // namespace
