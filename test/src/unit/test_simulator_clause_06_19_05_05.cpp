// §6.19.5.5: Num()

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
// §6.19.5.5: num() — returns the number of enum members
// =============================================================================
TEST(EnumMethods, NumReturnsCount) {
  EnumFixture f;
  f.RegisterEnum("color", "color_t", {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  auto* call = f.MakeEnumMethodCall("color", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

}  // namespace
