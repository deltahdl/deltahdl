// Non-LRM tests

#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "simulation/sv_callable.h"

using namespace delta;

namespace {

// =============================================================================
// SvCallable
// =============================================================================
TEST(SvCallable, ConstructFunction_BasicProperties) {
  std::vector<CallableParam> params = {
      {"a", Direction::kInput, 8},
      {"b", Direction::kInput, 8},
  };
  SvCallable func("add", /*is_task=*/false, params, nullptr);
  EXPECT_EQ(func.Name(), "add");
  EXPECT_FALSE(func.IsTask());
  EXPECT_EQ(func.Params().size(), 2u);
  EXPECT_EQ(func.Body(), nullptr);
}

TEST(SvCallable, ConstructFunction_ParamDetails) {
  std::vector<CallableParam> params = {
      {"a", Direction::kInput, 8},
      {"b", Direction::kInput, 8},
  };
  SvCallable func("add", /*is_task=*/false, params, nullptr);
  EXPECT_EQ(func.Params()[0].name, "a");
  EXPECT_EQ(func.Params()[1].width, 8u);
}

TEST(SvCallable, ConstructTask) {
  SvCallable task("my_task", /*is_task=*/true, {}, nullptr);
  EXPECT_EQ(task.Name(), "my_task");
  EXPECT_TRUE(task.IsTask());
  EXPECT_TRUE(task.Params().empty());
}

TEST(SvCallable, ParamDirections) {
  std::vector<CallableParam> params = {
      {"in_param", Direction::kInput, 1},
      {"out_param", Direction::kOutput, 32},
      {"inout_param", Direction::kInout, 16},
  };
  SvCallable func("mixed", false, params, nullptr);
  EXPECT_EQ(func.Params()[0].direction, Direction::kInput);
  EXPECT_EQ(func.Params()[1].direction, Direction::kOutput);
  EXPECT_EQ(func.Params()[2].direction, Direction::kInout);
}

// =============================================================================
// SvCallableContext
// =============================================================================
TEST(SvCallableContext, EmptyStack) {
  SvCallableContext ctx;
  EXPECT_TRUE(ctx.Empty());
  EXPECT_EQ(ctx.Depth(), 0u);
  EXPECT_EQ(ctx.CurrentFrame(), nullptr);
}

TEST(SvCallableContext, PushFrame) {
  SvCallableContext ctx;
  CallFrame frame;
  frame.callable_name = "test_func";
  frame.caller_id = 42;

  ctx.PushFrame(frame);
  EXPECT_FALSE(ctx.Empty());
  EXPECT_EQ(ctx.Depth(), 1u);
  ASSERT_NE(ctx.CurrentFrame(), nullptr);
  EXPECT_EQ(ctx.CurrentFrame()->callable_name, "test_func");
  EXPECT_EQ(ctx.CurrentFrame()->caller_id, 42u);
}

TEST(SvCallableContext, PopFrame) {
  SvCallableContext ctx;
  CallFrame frame;
  frame.callable_name = "test_func";
  frame.caller_id = 42;
  ctx.PushFrame(frame);

  ctx.PopFrame();
  EXPECT_TRUE(ctx.Empty());
  EXPECT_EQ(ctx.Depth(), 0u);
}

TEST(SvCallableContext, NestedCalls) {
  SvCallableContext ctx;

  CallFrame outer;
  outer.callable_name = "outer";
  ctx.PushFrame(outer);

  CallFrame inner;
  inner.callable_name = "inner";
  ctx.PushFrame(inner);

  EXPECT_EQ(ctx.Depth(), 2u);
  EXPECT_EQ(ctx.CurrentFrame()->callable_name, "inner");

  ctx.PopFrame();
  EXPECT_EQ(ctx.CurrentFrame()->callable_name, "outer");

  ctx.PopFrame();
  EXPECT_TRUE(ctx.Empty());
}

}  // namespace
