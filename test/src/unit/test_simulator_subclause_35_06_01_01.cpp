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
// tests observe DpiRuntime::MakeOpenArrayFromActual deriving the open-array
// formal's range from the actual presented at each call.

// §35.6.1.1: "The unsized ranges of open arrays are determined at a call site."
// The same open-array formal, given actuals of different sizes at two call
// sites, reports each actual's size -- the formal's range follows the actual,
// not a fixed declaration.
TEST(DpiWysiwygOpenArray, CallSiteDeterminesOpenArrayFormalSize) {
  SvOpenArrayHandle small =
      DpiRuntime::MakeOpenArrayFromActual(nullptr, 10, 32);
  SvOpenArrayHandle large =
      DpiRuntime::MakeOpenArrayFromActual(nullptr, 64, 32);

  EXPECT_EQ(DpiRuntime::SvSize(small), 10u);
  EXPECT_EQ(DpiRuntime::SvHigh(small), 9u);

  EXPECT_EQ(DpiRuntime::SvSize(large), 64u);
  EXPECT_EQ(DpiRuntime::SvHigh(large), 63u);
}

// §35.6.1.1: "A solitary, unsized, packed dimension assumes the linearized,
// normalized range of the actual's packed dimensions." The handle's range is
// reported in normalized form -- low fixed at 0 and high at size-1 -- whatever
// the actual's size.
TEST(DpiWysiwygOpenArray, SolitaryUnsizedDimUsesNormalizedRange) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromActual(nullptr, 8, 16);

  EXPECT_EQ(DpiRuntime::SvLow(h), 0u);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 7u);
  EXPECT_EQ(DpiRuntime::SvSize(h), 8u);
}

// §35.6.1.1: "the rest of the type information is specified at the import
// declaration." Only the unsized range varies with the actual; the element
// width carried from the import declaration is preserved across call sites,
// even as the size differs between them.
TEST(DpiWysiwygOpenArray, DeclaredTypeInfoSurvivesAcrossCallSites) {
  SvOpenArrayHandle a = DpiRuntime::MakeOpenArrayFromActual(nullptr, 4, 32);
  SvOpenArrayHandle b = DpiRuntime::MakeOpenArrayFromActual(nullptr, 100, 32);

  EXPECT_EQ(a.elem_width, 32u);
  EXPECT_EQ(b.elem_width, 32u);
  EXPECT_NE(DpiRuntime::SvSize(a), DpiRuntime::SvSize(b));
}

// §35.6.1.1: an empty actual is a valid call site -- a zero-size open array
// yields a well-formed, empty handle rather than an error.
TEST(DpiWysiwygOpenArray, EmptyActualYieldsEmptyOpenArray) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromActual(nullptr, 0, 32);

  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
  EXPECT_EQ(DpiRuntime::SvLow(h), 0u);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 0u);
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

}  // namespace
