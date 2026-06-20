#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_enum_methods.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EnumMethods, PrevReturnsPrevMember) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EnumMethods, PrevWrapsFromFirst) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(EnumMethods, PrevWithCount) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call =
      f.MakeEnumMethodCallWithArgs("color", "prev", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EnumMethods, PrevOnNonMemberValue) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto* call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EnumMethods, PrevFullIteration) {
  EnumFixture f;
  auto* var =
      f.RegisterEnum("state", "state_t", {{"A", 10}, {"B", 20}, {"C", 30}});
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  std::vector<uint64_t> visited;
  for (int i = 0; i < 4; ++i) {
    visited.push_back(var->value.ToUint64());
    auto* call = f.MakeEnumMethodCall("state", "prev");
    auto result = EvalExpr(call, f.ctx, f.arena);
    var->value = result;
  }
  EXPECT_EQ(visited, (std::vector<uint64_t>{10, 30, 20, 10}));
}

// A step count of zero is honored literally: no movement from the current
// member.
TEST(EnumMethods, PrevByZeroReturnsCurrent) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call =
      f.MakeEnumMethodCallWithArgs("color", "prev", {f.MakeIntLiteral(0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// A step count larger than the enumeration size reduces modulo the member
// count, so stepping back by 4 in a 3-member enum matches stepping back by 1.
TEST(EnumMethods, PrevCountExceedingSizeWraps) {
  EnumFixture f;
  auto* var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call =
      f.MakeEnumMethodCallWithArgs("color", "prev", {f.MakeIntLiteral(4)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// In a single-member enumeration the previous value wraps back to that one
// member.
TEST(EnumMethods, PrevSingleMemberReturnsSelf) {
  EnumFixture f;
  auto* var = f.RegisterEnum("only", "only_t", {{"ONLY", 5}});
  var->value = MakeLogic4VecVal(f.arena, 32, 5);
  auto* call = f.MakeEnumMethodCall("only", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
}

}  // namespace
