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

TEST(DpiRuntime, ArgValueString) {
  auto v = DpiArgValue::FromString("hello");
  EXPECT_EQ(v.type, DataTypeKind::kString);
  EXPECT_EQ(v.AsString(), "hello");
}

// =============================================================================
// DpiRuntime: scope management (svGetScope, svSetScope)
// =============================================================================
TEST(DpiRuntime, ScopeManagement) {
  DpiRuntime rt;
  EXPECT_EQ(rt.CurrentScope(), nullptr);

  DpiScope scope;
  scope.name = "top.dut";
  scope.module_name = "dut";
  rt.PushScope(scope);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut");

  DpiScope inner;
  inner.name = "top.dut.sub";
  inner.module_name = "sub";
  rt.PushScope(inner);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut.sub");

  rt.PopScope();
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut");

  rt.PopScope();
  EXPECT_EQ(rt.CurrentScope(), nullptr);
}

}  // namespace
