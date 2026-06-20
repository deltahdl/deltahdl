#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

// first() reports the first member, not whatever the variable currently
// holds: move the variable to a later member and confirm the result is
// unchanged.
TEST(EnumMethods, FirstIgnoresCurrentValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);  // currently BLUE
  auto* call = f.MakeEnumMethodCall("color", "first");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// The first member is decided by declaration order, never by the smallest
// numeric value: here the first member outranks every later one.
TEST(EnumMethods, FirstFollowsDeclarationOrderNotMinimum) {
  EnumFixture f;
  f.RegisterEnum("level", "level_t", {{"HIGH", 100}, {"MID", 50}, {"LOW", 1}});
  auto* call = f.MakeEnumMethodCall("level", "first");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 100u);
}

// A single-member enumeration: the only member is also the first.
TEST(EnumMethods, FirstWithSingleMember) {
  EnumFixture f;
  f.RegisterEnum("solo", "solo_t", {{"ONLY", 7}});
  auto* call = f.MakeEnumMethodCall("solo", "first");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

}  // namespace
