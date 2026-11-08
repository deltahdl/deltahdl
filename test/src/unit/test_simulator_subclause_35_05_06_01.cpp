#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiOpenArrayMatching, ActualMatchesOpenFormalRegardlessOfRange) {
  for (uint32_t sz : {1u, 5u, 33u, 256u}) {
    SvOpenArrayHandle h =
        DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, sz, 8);
    EXPECT_EQ(DpiRuntime::SvSize(h), sz);
    EXPECT_EQ(DpiRuntime::SvHigh(h), static_cast<int32_t>(sz) - 1);
  }
}

TEST(DpiOpenArrayMatching, ZeroLengthActualStillMatches) {
  SvOpenArrayHandle h =
      DpiRuntime::MakeOpenArrayFromPackedActual(nullptr, 0, 8);
  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
}

}  // namespace
