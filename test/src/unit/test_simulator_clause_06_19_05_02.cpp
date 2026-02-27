// §6.19.5.2: Last()

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
// §6.19.5.2: last() — returns the last member of the enum
// =============================================================================
TEST(EnumMethods, LastReturnsLastMember) {
  EnumFixture f;
  f.RegisterEnum("color", "color_t", {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  auto* call = f.MakeEnumMethodCall("color", "last");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(EnumMethods, LastWithGaps) {
  EnumFixture f;
  f.RegisterEnum("prio", "prio_t", {{"LOW", 1}, {"MED", 5}, {"HIGH", 100}});
  auto* call = f.MakeEnumMethodCall("prio", "last");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 100u);
}

}  // namespace
