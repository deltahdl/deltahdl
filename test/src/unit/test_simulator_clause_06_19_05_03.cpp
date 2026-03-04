#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(EnumMethods, NextReturnsNextMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* call = f.MakeEnumMethodCall("color", "next");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EnumMethods, NextFromMiddle) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call = f.MakeEnumMethodCall("color", "next");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(EnumMethods, NextWrapsFromLast) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call = f.MakeEnumMethodCall("color", "next");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EnumMethods, NextWithCount) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* call =
      f.MakeEnumMethodCallWithArgs("color", "next", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(EnumMethods, NextWithCountWraps) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call =
      f.MakeEnumMethodCallWithArgs("color", "next", {f.MakeIntLiteral(3)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EnumMethods, NextOnNonMemberValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});

  var->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto* call = f.MakeEnumMethodCall("color", "next");
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EnumMethods, FullIteration) {

  EnumFixture f;
  auto* var = f.RegisterEnum("state", "state_t",
                             {{"A", 10}, {"B", 20}, {"C", 30}, {"D", 40}});
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  std::vector<uint64_t> visited;
  for (int i = 0; i < 5; ++i) {
    visited.push_back(var->value.ToUint64());
    auto* call = f.MakeEnumMethodCall("state", "next");
    auto result = EvalExpr(call, f.ctx, f.arena);
    var->value = result;
  }
  EXPECT_EQ(visited, (std::vector<uint64_t>{10, 20, 30, 40, 10}));
}

}
