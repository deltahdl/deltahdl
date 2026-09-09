#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "helpers_dpi_take_int.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.6.1.1 — WYSIWYG principle. For a non-open formal the actual is guaranteed
// to be of the type specified at the import declaration, but the unsized ranges
// of an *open array* (§35.5.6.1) are statically unknown and are instead
// determined at the call site from the corresponding actual argument. These
// tests observe DpiRuntime::MakeOpenArrayFromPackedActual and
// MakeOpenArrayFromUnpackedActual deriving the open-array formal's range from
// the actual presented at each call, each by the rule the clause gives its own
// kind of unsized dimension.

// §35.6.1.1: "The unsized ranges of open arrays are determined at a call site."
// The same open-array formal, given actuals of different sizes at two call
// sites, reports each actual's size -- the formal's range follows the actual,
// not a fixed declaration.
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

// §35.6.1.1: "A solitary, unsized, packed dimension assumes the linearized,
// normalized range of the actual's packed dimensions." The handle's range is
// reported in normalized form -- low fixed at 0 and high at size-1 -- whatever
// the actual's size.
TEST(DpiWysiwygOpenArray, SolitaryUnsizedDimUsesNormalizedRange) {
  SvOpenArrayHandle h =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 8, 16);

  EXPECT_EQ(DpiRuntime::SvLow(h), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 7);
  EXPECT_EQ(DpiRuntime::SvSize(h), 8u);
}

// §35.6.1.1: "the rest of the type information is specified at the import
// declaration." Only the unsized range varies with the actual; the element
// width carried from the import declaration is preserved across call sites,
// even as the size differs between them.
TEST(DpiWysiwygOpenArray, DeclaredTypeInfoSurvivesAcrossCallSites) {
  SvOpenArrayHandle a =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 4, 32);
  SvOpenArrayHandle b =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 100, 32);

  EXPECT_EQ(a.elem_width, 32u);
  EXPECT_EQ(b.elem_width, 32u);
  EXPECT_NE(DpiRuntime::SvSize(a), DpiRuntime::SvSize(b));
}

// §35.6.1.1: an empty actual is a valid call site -- a zero-size open array
// yields a well-formed, empty handle rather than an error.
TEST(DpiWysiwygOpenArray, EmptyActualYieldsEmptyOpenArray) {
  SvOpenArrayHandle h =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 0, 32);

  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
  EXPECT_EQ(DpiRuntime::SvLow(h), 0);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 0);
}

// §35.6.1.1: under WYSIWYG a formal that is *not* an open array is fully
// defined by the import declaration -- the foreign function is guaranteed to
// receive the formal's declared type, never the actual's. A wider actual
// (longint) bound to a narrower declared formal (int) reaches the callee as the
// declared int, with no compiler coercion blending the caller's and callee's
// formals: the type comes solely from the import declaration site.
TEST(DpiWysiwygOpenArray, NonOpenFormalSeenAsDeclaredType) {
  DpiRuntime rt;
  // The callee reports the value only if it observed the declared int formal.
  DpiArgValue result =
      CallTakeIntReportingFormal(rt, DpiArgValue::FromLongint(7));

  EXPECT_EQ(result.AsInt(), 7);
}

// §35.6.1.1: "A formal's unsized, unpacked dimensions take on the ranges of the
// corresponding actual dimension." §35.5.6.1 declares `MyType a_10x5
// [11:20][6:2]` and binds it to `MyType i [][]`, so the formal's first
// dimension runs 11 to 20 -- the actual's own bounds, not a range built from
// its size.
TEST(DpiWysiwygOpenArray, UnpackedDimensionTakesTheActualsOwnRange) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{11, 20}, 32);

  // 0 and 9 are what the normalized range of a ten-element dimension would be,
  // which is the answer the packed rule gives and this one does not.
  EXPECT_EQ(DpiRuntime::SvLow(h), 11);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 20);
  EXPECT_EQ(DpiRuntime::SvSize(h), 10u);
}

// It is the range the formal takes on and not the size: two actuals of the same
// ten elements, declared over different bounds, give the one open formal two
// different ranges at the two call sites.
TEST(DpiWysiwygOpenArray, TwoActualsOfOneSizeGiveTheirOwnRanges) {
  SvOpenArrayHandle high = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{11, 20}, 32);
  SvOpenArrayHandle from_one = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{1, 10}, 32);

  EXPECT_EQ(DpiRuntime::SvSize(high), DpiRuntime::SvSize(from_one));
  EXPECT_EQ(DpiRuntime::SvLow(high), 11);
  EXPECT_EQ(DpiRuntime::SvLow(from_one), 1);
}

// §35.5.6.1's other actual for the same formal is `MyType a_64x8
// [64:1][-1:-8]`, whose second dimension runs -8 to -1. A range the formal
// takes on whole carries those bounds as they stand, which a range reported
// unsigned or built from the dimension's size cannot.
TEST(DpiWysiwygOpenArray, AnUnpackedDimensionsNegativeBoundsSurvive) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromUnpackedActual(
      nullptr, SvActualDimension{-8, -1}, 32);

  EXPECT_EQ(DpiRuntime::SvLow(h), -8);
  EXPECT_EQ(DpiRuntime::SvHigh(h), -1);
  EXPECT_EQ(DpiRuntime::SvSize(h), 8u);
}

// The contrast the clause draws between its two unsized dimensions, asked of
// one actual dimension: `[11:20]` reaches an unsized unpacked formal dimension
// as 11 to 20 and an actual's packed dimensions reach a solitary unsized packed
// one linearized and normalized, which for the same ten elements is 0 to 9.
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
