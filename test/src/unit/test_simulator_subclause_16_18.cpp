#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

// §16.18 "Clocking blocks and concurrent assertions".
//
// When a variable used in a concurrent assertion is a clocking block variable,
// it is sampled only in the clocking block: the assertion observes the value
// the block captured at its own clocking event, not a fresh sample of the
// underlying signal. This is not a special assertion-only mechanism -- a
// concurrent assertion evaluates its boolean operand through the ordinary
// expression path (the lowered clocked assert runs `EvalExpr(assert_expr,
// ...)`; see stmt_exec.cpp), and that path already routes a clocking-block
// member access to the block's sampled value (eval_expr.cpp
// TryClockvarMemberAccess -> ClockingManager::GetSampledValue). So the rule
// holds simply because the operand read goes through the real clocking-member
// read path.
//
// These tests observe that real production path. A live ClockingManager (the
// §14.4 production class) samples the signal at a clocking event; the
// underlying signal then moves on with no further clocking event, so the
// block's captured sample diverges from the live value. The operand is
// evaluated exactly as the lowered concurrent assert evaluates its boolean --
// EvalExpr over the member access the parser produces for `cb.a` -- and the
// value read is the block sample, not the live signal. Clocking blocks are
// attached through the same ClockingManager/EvalExpr harness every §14.x
// runtime clocking test uses, because the value the rule depends on is produced
// by that block's sampling, not by the syntactic form of the operand.

using namespace delta;

namespace {

// Build the member-access expression the parser emits for `block.signal`, the
// operand shape that reaches the clocking-member read path.
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

// Sample a one-bit input `a` into clocking block `cb` at a posedge, then drop
// the live signal after the clocking event with no further edge, so the block's
// captured sample stays put while the underlying signal moves on. The caller
// owns `cmgr` so it stays alive for the operand read that follows.
void SampleThenDropSignal(SimFixture& f, ClockingManager& cmgr,
                          uint64_t sampled_high) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* a = f.ctx.CreateVariable("a", 1);
  a->value = MakeLogic4VecVal(f.arena, 1, sampled_high);

  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "a", ClockingDir::kInput});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);  // clocking event captures a == sampled_high

  // The signal changes after the clocking event with no intervening edge, so
  // the block sample must not follow it.
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [a, &f, sampled_high]() {
    a->value = MakeLogic4VecVal(f.arena, 1, sampled_high ? 0 : 1);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev);

  f.scheduler.Run();
}

// §16.18: a concurrent-assertion operand that names a clocking-block variable
// reads the value sampled in the clocking block, not a fresh sample of the
// underlying signal. The block captured a == 1 at its clocking event; the live
// signal is then driven to 0. Evaluating the operand as the lowered assert does
// yields the block's 1, diverging from the live 0.
TEST(ClockingConcurrentAssertion, ClockingVariableInAssertionReadsBlockSample) {
  SimFixture f;
  ClockingManager cmgr;
  SampleThenDropSignal(f, cmgr, /*sampled_high=*/1);

  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0u);  // live signal has moved on

  auto used = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  EXPECT_EQ(used.ToUint64(), 1u);  // the value the clocking block sampled
  EXPECT_NE(used.ToUint64(), a->value.ToUint64());
}

// §16.18 holds for a clocking-block variable of any width, not just a one-bit
// boolean condition. A multi-bit clocking input used in a concurrent assertion
// is read at the value the block sampled -- carried at the signal's full width
// -- rather than a fresh read of the underlying vector. The block captures 0xA5
// at its clocking event; the underlying vector is then driven to 0x3C, and the
// operand read still yields the sampled 0xA5.
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

  SchedulePosedge(f, clk, 10);  // block captures data == 0xA5

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(data->value.ToUint64(), 0x3Cu);  // live vector has moved on

  auto used = EvalExpr(MakeClockvarOperand(f, "cb", "data"), f.ctx, f.arena);
  EXPECT_EQ(used.ToUint64(), 0xA5u);  // the full-width value the block sampled
  EXPECT_NE(used.ToUint64(), data->value.ToUint64());
}

// §16.18 applies only to clocking-block variables. A plain variable used in the
// same assertion is not redirected to any clocking-block sample: it reads its
// own value. Here `a` (a clocking-block input) reads the block's frozen sample
// while `b` (an ordinary variable) reads its live value.
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

  SchedulePosedge(f, clk, 10);  // block captures a == 1

  // Both signals drop after the clocking event.
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [a, b, &f]() {
    a->value = MakeLogic4VecVal(f.arena, 1, 0);
    b->value = MakeLogic4VecVal(f.arena, 1, 0);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev);
  f.scheduler.Run();

  // The clocking-block variable reads the block's frozen sample...
  auto clk_var = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  EXPECT_EQ(clk_var.ToUint64(), 1u);
  // ...but the plain variable, though used in the same assertion, is sampled
  // nowhere in a clocking block and reads its live value.
  auto plain = EvalExpr(MakePlainOperand(f, "b"), f.ctx, f.arena);
  EXPECT_EQ(plain.ToUint64(), 0u);
  EXPECT_NE(clk_var.ToUint64(), plain.ToUint64());
}

// §16.18 (a1/a2/a3/a4 equivalence of the LRM example): because a clocking-block
// variable is sampled only in the clocking block, every reference to it in an
// assertion observes that single captured value. Independent operand
// expressions naming the same clocking variable agree with each other and with
// the block's own stored sample.
TEST(ClockingConcurrentAssertion, AllNamingsObserveTheSameBlockSample) {
  SimFixture f;
  ClockingManager cmgr;
  SampleThenDropSignal(f, cmgr, /*sampled_high=*/1);

  auto* mgr = f.ctx.GetClockingManager();
  ASSERT_NE(mgr, nullptr);

  auto naming1 = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  auto naming2 = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);

  EXPECT_EQ(naming1.ToUint64(), 1u);
  EXPECT_EQ(naming2.ToUint64(), naming1.ToUint64());
  // Both operand reads observe the one value the block sampled.
  EXPECT_EQ(naming1.ToUint64(), mgr->GetSampledValue("cb", "a"));
}

// §16.18 edge case: the clocking block's captured value is what the assertion
// reads even when that value is 0. The block samples a == 0 at its clocking
// event; the live signal is then driven to 1. The operand still reads the
// block's 0, not the live 1 -- a genuinely sampled 0 overrides the live value
// rather than the assertion re-sampling the underlying signal.
TEST(ClockingConcurrentAssertion, ZeroBlockSampleInAssertionOverridesLive) {
  SimFixture f;
  ClockingManager cmgr;
  SampleThenDropSignal(f, cmgr, /*sampled_high=*/0);

  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);  // live signal is now high

  auto used = EvalExpr(MakeClockvarOperand(f, "cb", "a"), f.ctx, f.arena);
  EXPECT_EQ(used.ToUint64(), 0u);  // the clocking block sampled 0
  EXPECT_NE(used.ToUint64(), a->value.ToUint64());
}

}  // namespace
