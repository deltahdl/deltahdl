#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

Expr* MakeClockvarOperand(SimFixture& f, const char* block,
                          const char* signal) {
  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = f.arena.Create<Expr>();
  access->lhs->kind = ExprKind::kIdentifier;
  access->lhs->text = block;
  access->rhs = f.arena.Create<Expr>();
  access->rhs->kind = ExprKind::kIdentifier;
  access->rhs->text = signal;
  return access;
}

Expr* MakePlainOperand(SimFixture& f, const char* name) {
  auto* id = f.arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name;
  return id;
}

void SampleThenDropSignal(SimFixture& f, ClockingManager& cmgr,
                          uint64_t sampled_high) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* a = f.ctx.CreateVariable("a", 1);
  a->value = MakeLogic4VecVal(f.arena, 1, sampled_high);

  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "a", ClockingDir::kInput});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [a, &f, sampled_high]() {
    a->value = MakeLogic4VecVal(f.arena, 1, sampled_high ? 0 : 1);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev);

  f.scheduler.Run();
}

TEST(ClockingConcurrentAssertion, ClockingVariableInAssertionReadsBlockSample) {
  SimFixture f;
  ClockingManager cmgr;
  SampleThenDropSignal(f, cmgr, 1);

  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0u);

  auto used = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  EXPECT_EQ(used.ToUint64(), 1u);
  EXPECT_NE(used.ToUint64(), a->value.ToUint64());
}

TEST(ClockingConcurrentAssertion,
     MultiBitClockingVariableInAssertionReadsBlockSample) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xA5);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(data->value.ToUint64(), 0x3Cu);

  auto used = EvalExpr(MakeClockvarOperand(f, "cb", "data"), f.ctx, f.arena);
  EXPECT_EQ(used.ToUint64(), 0xA5u);
  EXPECT_NE(used.ToUint64(), data->value.ToUint64());
}

TEST(ClockingConcurrentAssertion, PlainVariableInAssertionIsNotRedirected) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* a = f.ctx.CreateVariable("a", 1);
  a->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* b = f.ctx.CreateVariable("b", 1);
  b->value = MakeLogic4VecVal(f.arena, 1, 1);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "a", ClockingDir::kInput});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [a, b, &f]() {
    a->value = MakeLogic4VecVal(f.arena, 1, 0);
    b->value = MakeLogic4VecVal(f.arena, 1, 0);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev);
  f.scheduler.Run();

  auto clk_var = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  EXPECT_EQ(clk_var.ToUint64(), 1u);
  auto plain = EvalExpr(MakePlainOperand(f, "b"), f.ctx, f.arena);
  EXPECT_EQ(plain.ToUint64(), 0u);
  EXPECT_NE(clk_var.ToUint64(), plain.ToUint64());
}

TEST(ClockingConcurrentAssertion, AllNamingsObserveTheSameBlockSample) {
  SimFixture f;
  ClockingManager cmgr;
  SampleThenDropSignal(f, cmgr, 1);

  auto* mgr = f.ctx.GetClockingManager();
  ASSERT_NE(mgr, nullptr);

  auto naming1 = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  auto naming2 = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);

  EXPECT_EQ(naming1.ToUint64(), 1u);
  EXPECT_EQ(naming2.ToUint64(), naming1.ToUint64());
  EXPECT_EQ(naming1.ToUint64(), mgr->GetSampledValue("cb", "a"));
}

TEST(ClockingConcurrentAssertion, ZeroBlockSampleInAssertionOverridesLive) {
  SimFixture f;
  ClockingManager cmgr;
  SampleThenDropSignal(f, cmgr, 0);

  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);

  auto used = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  EXPECT_EQ(used.ToUint64(), 0u);
  EXPECT_NE(used.ToUint64(), a->value.ToUint64());
}

}  // namespace
