#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

// A single-member enumeration: the only member is both first and last.
TEST(EnumMethods, LastSingleMember) {
  EnumFixture f;
  f.RegisterEnum("solo", "solo_t", {{"ONLY", 7}});
  auto* call = f.MakeEnumMethodCall("solo", "last");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// last() reports the final member regardless of the variable's current value,
// unlike the relative next()/prev() methods.
TEST(EnumMethods, LastIgnoresCurrentValue) {
  EnumFixture f;
  auto* var =
      f.RegisterEnum("color", "color_t", {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);  // hold the middle member
  auto* call = f.MakeEnumMethodCall("color", "last");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

}
