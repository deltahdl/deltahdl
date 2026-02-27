// §6.19.5.1: First()

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"

using namespace delta;

// =============================================================================
// Test fixture: sets up SimContext with an enum type and variable
// =============================================================================
namespace {

// =============================================================================
// §6.19.5.1: first() — returns the first member of the enum
// =============================================================================
TEST(EnumMethods, FirstReturnsFirstMember) {
  EnumFixture f;
  f.RegisterEnum("color", "color_t", {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  auto* call = f.MakeEnumMethodCall("color", "first");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EnumMethods, FirstWithNonZeroStart) {
  EnumFixture f;
  f.RegisterEnum("status", "status_t",
                 {{"IDLE", 5}, {"ACTIVE", 10}, {"DONE", 15}});
  auto* call = f.MakeEnumMethodCall("status", "first");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
}

}  // namespace
