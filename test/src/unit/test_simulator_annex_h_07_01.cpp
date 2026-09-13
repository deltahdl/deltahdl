#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.7.1 (Limitations): packed arrays can have any number of dimensions
// but are always equivalent to a one-dimensional packed array and treated as
// such. The compiler linearizes a multidimensional packed part in the type of
// a formal, and, although an open array generally keeps the actual's original
// ranges, an actual whose packed part is multidimensional is linearized and
// normalized into the equivalent one-dimensional packed array (§H.7.5). The
// cases check the size that array has for one, two and three packed
// dimensions however their ranges run, the normalized range the open-array
// formal then takes, and, against it, that an unpacked dimension keeps the
// actual's own range -- the note of the subclause has an actual carry both
// parts, either multidimensional.

namespace {

// §H.7.1: the linearized size is the product of the dimensions' sizes,
// whichever way each range runs; no dimensions give no elements.
TEST(PackedArrayLinearization, TheSizeIsTheProductOfTheDimensions) {
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{0, 7}}), 8u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{7, 0}}), 8u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{3, 0}, {7, 0}}), 32u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{0, 1}, {2, 0}, {3, 0}}), 24u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{5, 5}}), 1u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({{-2, 1}, {7, 0}}), 32u);
  EXPECT_EQ(DpiRuntime::LinearizedPackedSize({}), 0u);
}

// §H.7.1 with §H.7.5: an open-array formal bound to an actual with a
// multidimensional packed part takes the linearized, normalized range 0 to
// size-1, whatever ranges the actual's dimensions ran over; the original
// packed ranges are not kept.
TEST(PackedArrayLinearization, TheFormalTakesTheNormalizedOneDimensionalRange) {
  std::array<uint32_t, 1> words{};
  const SvOpenArrayHandle kTwo = DpiRuntime::MakeOpenArrayFromPackedActual(
      words.data(), {{3, 0}, {7, 0}}, /*elem_width=*/1);
  EXPECT_EQ(DpiRuntime::SvSize(kTwo), 32u);
  EXPECT_EQ(DpiRuntime::SvLow(kTwo), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(kTwo), 31);
  const SvOpenArrayHandle kShifted = DpiRuntime::MakeOpenArrayFromPackedActual(
      words.data(), {{9, 8}, {15, 12}}, /*elem_width=*/1);
  EXPECT_EQ(DpiRuntime::SvSize(kShifted), 8u);
  EXPECT_EQ(DpiRuntime::SvLow(kShifted), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(kShifted), 7);
  // The same as handing over the count already linearized.
  const SvOpenArrayHandle kCounted =
      DpiRuntime::MakeOpenArrayFromPackedActual(words.data(), 8u,
                                                /*elem_width=*/1);
  EXPECT_EQ(DpiRuntime::SvSize(kCounted), DpiRuntime::SvSize(kShifted));
  EXPECT_EQ(DpiRuntime::SvHigh(kCounted), DpiRuntime::SvHigh(kShifted));
}

// §H.7.1: the original ranges are generally preserved for open arrays, and it
// is the packed part alone that is linearized and normalized: an unpacked
// dimension of the same actual keeps its own range.
TEST(PackedArrayLinearization, AnUnpackedDimensionKeepsItsOwnRange) {
  std::array<uint32_t, 10> words{};
  const SvOpenArrayHandle kUnpacked =
      DpiRuntime::MakeOpenArrayFromUnpackedActual(words.data(), {11, 20},
                                                  /*elem_width=*/32);
  EXPECT_EQ(DpiRuntime::SvSize(kUnpacked), 10u);
  EXPECT_EQ(DpiRuntime::SvLow(kUnpacked), 11);
  EXPECT_EQ(DpiRuntime::SvHigh(kUnpacked), 20);
  const SvOpenArrayHandle kPacked = DpiRuntime::MakeOpenArrayFromPackedActual(
      words.data(), {{11, 20}}, /*elem_width=*/1);
  EXPECT_EQ(DpiRuntime::SvSize(kPacked), 10u);
  EXPECT_EQ(DpiRuntime::SvLow(kPacked), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(kPacked), 9);
}

}  // namespace
