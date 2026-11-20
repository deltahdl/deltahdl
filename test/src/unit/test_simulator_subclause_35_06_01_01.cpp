#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <string>

#include "helpers_dpi_c_binding.h"
#include "helpers_dpi_take_int.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(DpiWysiwygOpenArray, CallSiteDeterminesOpenArrayFormalSize) {
  SvOpenArrayHandle small =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 10, 32);
  SvOpenArrayHandle large =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 64, 32);

  EXPECT_EQ(DpiRuntime::SvSize(small), 10u);
  EXPECT_EQ(DpiRuntime::SvHigh(small), 9);

  EXPECT_EQ(DpiRuntime::SvSize(large), 64u);
  EXPECT_EQ(DpiRuntime::SvHigh(large), 63);
}

TEST(DpiWysiwygOpenArray, SolitaryUnsizedDimUsesNormalizedRange) {
  SvOpenArrayHandle h =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 8, 16);

  EXPECT_EQ(DpiRuntime::SvLow(h), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 7);
  EXPECT_EQ(DpiRuntime::SvSize(h), 8u);
}

TEST(DpiWysiwygOpenArray, DeclaredTypeInfoSurvivesAcrossCallSites) {
  SvOpenArrayHandle a =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 4, 32);
  SvOpenArrayHandle b =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 100, 32);

  EXPECT_EQ(a.elem_width, 32u);
  EXPECT_EQ(b.elem_width, 32u);
  EXPECT_NE(DpiRuntime::SvSize(a), DpiRuntime::SvSize(b));
}

TEST(DpiWysiwygOpenArray, EmptyActualYieldsEmptyOpenArray) {
  SvOpenArrayHandle h =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 0, 32);

  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
  EXPECT_EQ(DpiRuntime::SvLow(h), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 0);
}

TEST(DpiWysiwygOpenArray, NonOpenFormalSeenAsDeclaredType) {
  DpiRuntime rt;
  DpiArgValue result =
      CallTakeIntReportingFormal(rt, DpiArgValue::FromLongint(7));

  EXPECT_EQ(result.AsInt(), 7);
}

TEST(DpiWysiwygOpenArray, UnpackedDimensionTakesTheActualsOwnRange) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{11, 20}, 32);

  EXPECT_EQ(DpiRuntime::SvLow(h), 11);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 20);
  EXPECT_EQ(DpiRuntime::SvSize(h), 10u);
}

TEST(DpiWysiwygOpenArray, TwoActualsOfOneSizeGiveTheirOwnRanges) {
  SvOpenArrayHandle high = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{11, 20}, 32);
  SvOpenArrayHandle from_one = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{1, 10}, 32);

  EXPECT_EQ(DpiRuntime::SvSize(high), DpiRuntime::SvSize(from_one));
  EXPECT_EQ(DpiRuntime::SvLow(high), 11);
  EXPECT_EQ(DpiRuntime::SvLow(from_one), 1);
}

TEST(DpiWysiwygOpenArray, AnUnpackedDimensionsNegativeBoundsSurvive) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{-8, -1}, 32);

  EXPECT_EQ(DpiRuntime::SvLow(h), -8);
  EXPECT_EQ(DpiRuntime::SvHigh(h), -1);
  EXPECT_EQ(DpiRuntime::SvSize(h), 8u);
}

TEST(DpiWysiwygOpenArray, ThePackedDimensionNormalizesWhereTheUnpackedDoesNot) {
  SvOpenArrayHandle unpacked = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{11, 20}, 32);
  SvOpenArrayHandle packed =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 10, 32);

  EXPECT_EQ(DpiRuntime::SvSize(unpacked), DpiRuntime::SvSize(packed));
  EXPECT_EQ(DpiRuntime::SvLow(unpacked), 11);
  EXPECT_EQ(DpiRuntime::SvLow(packed), 0);
}

int SumOfOpenArray(const svOpenArrayHandle h) {
  int sum = 0;
  for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
    auto* element = static_cast<int*>(svGetArrElemPtr1(h, i));
    if (element != nullptr) sum += *element;
  }
  return sum * 100 + svSize(h, 1);
}

int32_t OpenArraySum(const char* decl, const char* fill, const char* actual) {
  return IntVariableAfterRun(
      std::string("module top;\n"
                  "  import \"DPI-C\" function int c_sum(input "
                  "int a []);\n") +
          decl +
          "  int r;\n"
          "  initial begin\n" +
          fill + "    r = c_sum(" + actual +
          ");\n"
          "  end\n"
          "endmodule\n",
      {{"c_sum", reinterpret_cast<void*>(&SumOfOpenArray)}},
      "subclause_35_06_01_01_open", "r");
}

TEST(DpiOpenArrayInADesign, DISABLED_ADynamicArrayActualFillsAnOpenFormal) {
  EXPECT_EQ(OpenArraySum("  int d [];\n", "    d = '{4, 5, 6};\n", "d"), 1503);
}

TEST(DpiOpenArrayInADesign,
     DISABLED_ADynamicArrayResizedBetweenCallsSizesTheFormal) {
  EXPECT_EQ(OpenArraySum("  int d [];\n",
                         "    d = '{4, 5, 6};\n    void'(c_sum(d));\n"
                         "    d = new[5](d);\n",
                         "d"),
            1505);
}

TEST(DpiOpenArrayInADesign, AFixedArrayWithOffsetBoundsFillsAnOpenFormal) {
  EXPECT_EQ(OpenArraySum("  int s [2:4];\n", "    s = '{1, 2, 3};\n", "s"),
            603);
}

}  // namespace
