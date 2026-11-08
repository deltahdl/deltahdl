#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_open_array_natural_order.h"
#include "simulator/dpi_arg_value.h"
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

TEST(MappingSvRangesToCRanges, PackedRangeNormalizedLsbZeroMsbAbsLminusR) {
  struct Case {
    int l;
    int r;
  };
  const Case kCases[] = {{7, 4}, {4, 7}, {2, -3}};
  for (const Case& c : kCases) {
    const int kMsb = std::abs(c.l - c.r);
    const int kWidth = kMsb + 1;
    const int kWords = SV_PACKED_DATA_NELEMS(kWidth);
    ASSERT_LE(kWords, 2);
    svBitVecVal vec[2] = {0u, 0u};

    svPutBitselBit(vec, 0, 1);
    svPutBitselBit(vec, kMsb, 1);

    EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
    EXPECT_EQ(svGetBitselBit(vec, kMsb), 1u);

    for (int i = 0; i < kWidth; ++i) {
      const svBit kExpected = (i == 0 || i == kMsb) ? 1u : 0u;
      EXPECT_EQ(svGetBitselBit(vec, i), kExpected)
          << "L=" << c.l << " R=" << c.r;
    }
  }
}

TEST(MappingSvRangesToCRanges, SingleElementPackedRangeNormalizesToZeroZero) {
  const int kL = 5, kR = 5;
  EXPECT_EQ(std::abs(kL - kR), 0);

  svBitVecVal vec = 0u;
  svPutBitselBit(&vec, 0, 1);
  EXPECT_EQ(svGetBitselBit(&vec, 0), 1u);
  EXPECT_EQ(vec, 1u);
}

TEST(MappingSvRangesToCRanges, UnpackedNaturalOrderMinToZeroMaxToAbs) {
  struct Case {
    int l;
    int r;
  };
  const Case kCases[] = {{0, 7}, {7, 0}, {-1, -8}};
  for (const Case& c : kCases) {
    const SvOpenArrayDimRange kRanges[] = {{0, 0}, {c.l, c.r}};
    SvOpenArrayDesc desc;
    svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

    ExpectUnpackedNaturalOrderMinToZeroMaxToAbs(h, 1, c.l, c.r);
  }
}

TEST(MappingSvRangesToCRanges, UnpackedLowerIndicesGoFirst) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {3, -2}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  const int kLo = svLow(h, 1);
  const int kSize = svSize(h, 1);
  EXPECT_EQ(kLo, -2);
  EXPECT_EQ(kSize, 6);

  int expected_c = 0;
  for (int sv = kLo; sv < kLo + kSize; ++sv) {
    EXPECT_EQ(sv - kLo, expected_c);
    ++expected_c;
  }
  EXPECT_EQ(expected_c, kSize);
}

TEST(MappingSvRangesToCRanges, WorkedExampleNormalizedForm) {
  const int kPackedSizes[] = {std::abs(2 - 3) + 1, std::abs(1 - 3) + 1,
                              std::abs(2 - 0) + 1};
  int packed_width = 1;
  for (int s : kPackedSizes) packed_width *= s;
  EXPECT_EQ(packed_width, 18);

  const SvOpenArrayDimRange kRanges[] = {{17, 0}, {1, 10}, {31, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 3, &desc);

  EXPECT_EQ(svSize(h, 0), 18);
  EXPECT_EQ(std::abs(svLeft(h, 0) - svRight(h, 0)), 17);
  svBitVecVal packed = 0u;
  svPutBitselBit(&packed, 17, 1);
  EXPECT_EQ(svGetBitselBit(&packed, 17), 1u);

  EXPECT_EQ(svLow(h, 1), 1);
  EXPECT_EQ(svSize(h, 1), 10);
  EXPECT_EQ(svLow(h, 1) - svLow(h, 1), 0);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 9);

  EXPECT_EQ(svLow(h, 2), 0);
  EXPECT_EQ(svSize(h, 2), 32);
  EXPECT_EQ(svHigh(h, 2) - svLow(h, 2), 31);
}

TEST(MappingSvRangesToCRanges, MappingAppliesInBothCallDirections) {
  const int kL = 11, kR = 4;
  const int kMsb = std::abs(kL - kR);
  const int kWidth = kMsb + 1;
  svBitVecVal vec = 0u;

  for (int i = 0; i < kWidth; ++i) {
    if (i % 2 == 0) svPutBitselBit(&vec, i, 1);
  }

  for (int i = 0; i < kWidth; ++i) {
    EXPECT_EQ(svGetBitselBit(&vec, i),
              static_cast<svBit>(i % 2 == 0 ? 1u : 0u));
  }
  EXPECT_EQ(svGetBitselBit(&vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(&vec, kMsb), 0u);
}

TEST(MappingSvRangesToCRanges, PackedRangeWiderThanCanonicalWordNormalizes) {
  const int kL = 40, kR = 1;
  const int kMsb = std::abs(kL - kR);
  const int kWidth = kMsb + 1;
  ASSERT_EQ(SV_PACKED_DATA_NELEMS(kWidth), 2);
  svBitVecVal vec[2] = {0u, 0u};

  svPutBitselBit(vec, 0, 1);
  svPutBitselBit(vec, kMsb, 1);

  EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kMsb), 1u);
  EXPECT_EQ(vec[0], 1u);
  EXPECT_EQ(vec[1], 1u << 7);
}

TEST(MappingSvRangesToCRanges, SingleElementUnpackedDimensionMapsToZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {-4, -4}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(kRanges, 2, &desc);

  EXPECT_EQ(svLow(h, 1), -4);
  EXPECT_EQ(svHigh(h, 1), -4);
  EXPECT_EQ(svSize(h, 1), 1);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 0);
}

int WeightedByCIndex(const uint32_t* a) {
  return static_cast<int>(a[0] + (a[1] * 10) + (a[2] * 100) + (a[3] * 1000));
}

void FillThreeInts(int* o) {
  o[0] = 9;
  o[1] = 8;
  o[2] = 7;
}

void FillVectors(SvLogicVecVal* arr) {
  for (int i = 0; i < 64 * 2; ++i) arr[i] = {0, 0};
  arr[0].aval = 7;
  arr[(63 * 2) + 1].aval = 1U << 31U;
}

void RunSizedArrayDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function int weighted(input bit [7:0] a [0:3]);\n"
      "  import \"DPI-C\" function void fill_arr(output int o [3:1]);\n"
      "  import \"DPI-C\" function void fill_vecs(\n"
      "      output logic [64:1] arr [0:63]);\n"
      "  bit [7:0] a [0:3] = '{1, 2, 3, 4};\n"
      "  bit [7:0] r [3:0] = '{4, 3, 2, 1};\n"
      "  int o [3:1];\n"
      "  logic [64:1] v [0:63];\n"
      "  int w, w2;\n"
      "  initial begin\n"
      "    w = weighted(a);\n"
      "    w2 = weighted(r);\n"
      "    fill_arr(o);\n"
      "    fill_vecs(v);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"weighted", reinterpret_cast<void*>(&WeightedByCIndex)},
       {"fill_arr", reinterpret_cast<void*>(&FillThreeInts)},
       {"fill_vecs", reinterpret_cast<void*>(&FillVectors)}},
      "annex_h_07_06_sized_arrays");
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiArrayNaturalOrder, ASizedArrayCrossesInCLayoutLowerIndexFirst) {
  SimFixture f;
  RunSizedArrayDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "w"), 4321U);
  EXPECT_EQ(VariableValue(f, "w2"), 4321U);
}

TEST(DpiArrayNaturalOrder, ASizedOutputArrayIsCopiedBackLowerIndexFirst) {
  SimFixture f;
  RunSizedArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "o[1]"), 9U);
  EXPECT_EQ(VariableValue(f, "o[2]"), 8U);
  EXPECT_EQ(VariableValue(f, "o[3]"), 7U);
}

TEST(DpiArrayNaturalOrder, AnArrayOfVectorsCrossesAsTheirChunks) {
  SimFixture f;
  RunSizedArrayDesign(f);
  EXPECT_EQ(VariableValue(f, "v[0]"), 7U);
  EXPECT_EQ(VariableValue(f, "v[63]"), uint64_t{1} << 63U);
  EXPECT_EQ(VariableValue(f, "v[1]"), 0U);
}

int SumOfTwo(const int* a) { return (a[0] * 10) + a[1]; }

TEST(DpiArrayNaturalOrder, AParameterSizedArrayCrossesInCLayout) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  parameter int N = 2;\n"
      "  import \"DPI-C\" function int sum_sized(input int a [N]);\n"
      "  int arr [2] = '{3, 4};\n"
      "  int r;\n"
      "  initial r = sum_sized(arr);\n"
      "endmodule\n",
      f, {{"sum_sized", reinterpret_cast<void*>(&SumOfTwo)}},
      "annex_h_07_06_parameter_sized");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "r"), 34U);
}

}  // namespace
