#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

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

TEST(ArrayQueryingFunctions, LowHighSizeMatchTwentySevenSemanticsAscending) {
  const SvOpenArrayDimRange kRanges[] = {{15, 0}, {0, 7}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLow(h, 1), 0);
  EXPECT_EQ(svHigh(h, 1), 7);
  EXPECT_EQ(svSize(h, 1), 8);
}

TEST(ArrayQueryingFunctions, LowHighSizeMatchTwentySevenSemanticsDescending) {
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

TEST(ArrayQueryingFunctions, IncrementMatchesTwentySevenSemantics) {
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

}  // namespace
