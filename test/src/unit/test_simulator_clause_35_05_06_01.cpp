#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.5.6.1 — Open arrays. Specifying a formal as an open array is solely a
// relaxation of the argument-matching rules: an actual argument matches the
// open formal regardless of the range of its corresponding dimension. These
// tests observe DpiRuntime::MakeOpenArrayFromActual binding actuals of varied
// ranges to one open-array formal -- each is accepted and yields a handle that
// carries that actual's own range, never rejected for a range mismatch.

// §35.5.6.1: an actual shall match the open-array formal whatever its range.
// Actuals of several distinct sizes each bind successfully and report their own
// size, so the open formal accepts them all.
TEST(DpiOpenArrayMatching, ActualMatchesOpenFormalRegardlessOfRange) {
  for (uint32_t sz : {1u, 5u, 33u, 256u}) {
    SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromActual(nullptr, sz, 8);
    EXPECT_EQ(DpiRuntime::SvSize(h), sz);
    EXPECT_EQ(DpiRuntime::SvHigh(h), sz - 1);
  }
}

// §35.5.6.1: the relaxation extends to the degenerate case -- a zero-length
// actual still matches the open-array formal and yields a valid, empty handle.
TEST(DpiOpenArrayMatching, ZeroLengthActualStillMatches) {
  SvOpenArrayHandle h = DpiRuntime::MakeOpenArrayFromActual(nullptr, 0, 8);
  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
}

}  // namespace
