// Annex H.9.3: Working with DPI context tasks and functions in C code

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

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

// =============================================================================
// DPI scope functions (Annex I)
// =============================================================================
TEST(SvDpi, ScopeGetSetRoundTrip) {
  svScope old_scope = svGetScope();
  int dummy = 42;
  auto new_scope = reinterpret_cast<svScope>(&dummy);
  svScope prev = svSetScope(new_scope);
  EXPECT_EQ(prev, old_scope);
  EXPECT_EQ(svGetScope(), new_scope);
  svSetScope(old_scope);
}

}  // namespace
