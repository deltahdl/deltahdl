#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(PackedArrayLinearization, TheSizeIsTheProductOfTheDimensions) {
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{0, 7}}), 8u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{7, 0}}), 8u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{3, 0}, {7, 0}}), 32u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{0, 1}, {2, 0}, {3, 0}}), 24u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{5, 5}}), 1u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{-2, 1}, {7, 0}}), 32u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({}), 0u);
}

TEST(PackedArrayLinearization, TheFormalTakesTheNormalizedOneDimensionalRange) {
  std::array<uint32_t, 1> words{};
  const SvOpenArrayHandle kTwo = DpiRuntime::MakeOpenArrayFromPackedActual(
      words.data(), {{3, 0}, {7, 0}}, 1);
  EXPECT_EQ(DpiRuntime::SvSize(kTwo), 32u);
  EXPECT_EQ(DpiRuntime::SvLow(kTwo), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(kTwo), 31);
  const SvOpenArrayHandle kShifted = DpiRuntime::MakeOpenArrayFromPackedActual(
      words.data(), {{9, 8}, {15, 12}}, 1);
  EXPECT_EQ(DpiRuntime::SvSize(kShifted), 8u);
  EXPECT_EQ(DpiRuntime::SvLow(kShifted), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(kShifted), 7);
  const SvOpenArrayHandle kCounted =
      DpiRuntime::MakeOpenArrayFromPackedActual(words.data(), 8u, 1);
  EXPECT_EQ(DpiRuntime::SvSize(kCounted), DpiRuntime::SvSize(kShifted));
  EXPECT_EQ(DpiRuntime::SvHigh(kCounted), DpiRuntime::SvHigh(kShifted));
}

TEST(PackedArrayLinearization, AnUnpackedDimensionKeepsItsOwnRange) {
  std::array<uint32_t, 10> words{};
  const SvOpenArrayHandle kUnpacked =
      DpiRuntime::MakeOpenArrayFromUnpackedActual(words.data(), {11, 20}, 32);
  EXPECT_EQ(DpiRuntime::SvSize(kUnpacked), 10u);
  EXPECT_EQ(DpiRuntime::SvLow(kUnpacked), 11);
  EXPECT_EQ(DpiRuntime::SvHigh(kUnpacked), 20);
  const SvOpenArrayHandle kPacked =
      DpiRuntime::MakeOpenArrayFromPackedActual(words.data(), {{11, 20}}, 1);
  EXPECT_EQ(DpiRuntime::SvSize(kPacked), 10u);
  EXPECT_EQ(DpiRuntime::SvLow(kPacked), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(kPacked), 9);
}

}  // namespace
