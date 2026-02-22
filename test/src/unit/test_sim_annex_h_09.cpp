// Annex H.9: Context tasks and functions

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

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

TEST(DpiRuntime, SetAndGetScope) {
  DpiRuntime rt;
  DpiScope scope;
  scope.name = "top.mod";
  rt.PushScope(scope);

  const DpiScope* saved = rt.GetScope();
  ASSERT_NE(saved, nullptr);

  rt.PopScope();
  EXPECT_EQ(rt.CurrentScope(), nullptr);

  // Restore scope.
  rt.SetScope(saved);
  EXPECT_EQ(rt.GetScope(), saved);
}

TEST(DpiRuntime, PopEmptyScopeDoesNotCrash) {
  DpiRuntime rt;
  rt.PopScope();  // Should not crash.
  EXPECT_EQ(rt.CurrentScope(), nullptr);
}

}  // namespace
