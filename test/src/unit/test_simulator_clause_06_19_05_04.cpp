// §6.19.5.4: Prev()

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
// §6.19.5.4: prev(N) — returns the Nth previous member (default N=1)
// =============================================================================
TEST(EnumMethods, PrevReturnsPrevMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);  // BLUE
  auto* call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);  // GREEN
}

TEST(EnumMethods, PrevWrapsFromFirst) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0);  // RED
  auto* call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);  // wraps to BLUE
}

TEST(EnumMethods, PrevWithCount) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);  // BLUE
  auto* call =
      f.MakeEnumMethodCallWithArgs("color", "prev", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);  // RED (back 2 from BLUE)
}

TEST(EnumMethods, PrevOnNonMemberValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto* call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  // For invalid current value, prev() returns last member.
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(EnumMethods, PrevFullIteration) {
  // Verify prev() can iterate backwards and wrap around.
  EnumFixture f;
  auto* var =
      f.RegisterEnum("state", "state_t", {{"A", 10}, {"B", 20}, {"C", 30}});
  var->value = MakeLogic4VecVal(f.arena, 32, 10);  // A

  std::vector<uint64_t> visited;
  for (int i = 0; i < 4; ++i) {
    visited.push_back(var->value.ToUint64());
    auto* call = f.MakeEnumMethodCall("state", "prev");
    auto result = EvalExpr(call, f.ctx, f.arena);
    var->value = result;
  }
  EXPECT_EQ(visited, (std::vector<uint64_t>{10, 30, 20, 10}));
}

}  // namespace
