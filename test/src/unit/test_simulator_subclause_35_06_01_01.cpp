#include <gtest/gtest.h>

#include "helpers_dpi_take_int.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

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

}  // namespace
