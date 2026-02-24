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

TEST(DpiRuntime, ArgValueReal) {
  auto v = DpiArgValue::FromReal(3.14);
  EXPECT_EQ(v.type, DataTypeKind::kReal);
  EXPECT_DOUBLE_EQ(v.AsReal(), 3.14);
}

// =============================================================================
// DpiArgValue: typed argument construction and access
// =============================================================================
TEST(DpiRuntime, ArgValueInt) {
  auto v = DpiArgValue::FromInt(42);
  EXPECT_EQ(v.type, DataTypeKind::kInt);
  EXPECT_EQ(v.AsInt(), 42);
}

}  // namespace
