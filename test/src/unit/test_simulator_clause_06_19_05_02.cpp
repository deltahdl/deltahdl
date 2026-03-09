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

}  // namespace
