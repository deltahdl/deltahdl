// §non-lrm:dpi_helpers

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiRuntime, PopEmptyScopeDoesNotCrash) {
  DpiRuntime rt;
  rt.PopScope();  // Should not crash.
  EXPECT_EQ(rt.CurrentScope(), nullptr);
}

}  // namespace
