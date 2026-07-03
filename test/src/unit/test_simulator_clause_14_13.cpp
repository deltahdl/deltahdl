#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InputSamplingSim, PosedgeSamplesCurrentValue) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data_in", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data_in"), 0xABu);
}

TEST(InputSamplingSim, NegedgeSamplesCurrentValue) {
  SimFixture f;
  ClockingManager cmgr;
  TestNegedgeSampling(f, cmgr);
}

TEST(InputSamplingSim, SampledValueUpdatesAcrossEdges) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);

  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{12}, Region::kActive, ev_data);

  ScheduleNegedge(f, clk, 15);

  SchedulePosedge(f, clk, 20);

  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x22u);
}

TEST(InputSamplingSim, ZeroSkewInputSamplesInObservedRegion) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x10);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{0};
  sig.is_explicit_zero_skew = true;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  auto* ev_clk = f.scheduler.GetEventPool().Acquire();
  ev_clk->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev_clk);

  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev_data);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

// §14.13: a non-#0 (default) skew input samples the Postponed-region value from
// before the clocking event, so a same-time-step Active update to the signal
// after the edge is NOT reflected. This is the complement of the explicit-#0
// case (ZeroSkewInputSamplesInObservedRegion), which DOES observe that update
// because it samples in the Observed region after all Active events settle.
// Same stimulus, opposite result -- the only difference is
// is_explicit_zero_skew.
TEST(InputSamplingSim, NonZeroSkewInputDoesNotSampleSameStepActiveUpdate) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x10);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{0};
  // Default (non-explicit-#0) skew: sampled in the Active-region edge callback,
  // before the same-step data update runs.
  sig.is_explicit_zero_skew = false;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  // Clock edge scheduled first, data update second: both in the Active region
  // at t=10. The edge callback samples data before the update event fires.
  auto* ev_clk = f.scheduler.GetEventPool().Acquire();
  ev_clk->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev_clk);

  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev_data);

  f.scheduler.Run();

  // Postponed-region value from before the edge, not the same-step update.
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x10u);
}

// §14.13: a clockvar read yields the value sampled at the most recent clocking
// event, not the signal's live value. After the edge samples the signal, a
// later change to the underlying signal with no intervening clocking event
// leaves the sampled value frozen; reading cb.data through the real expression
// path still yields the old sample even though the live variable has moved on.
TEST(InputSamplingSim, ClockvarReadStaysFrozenBetweenEdges) {
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

  // Signal changes after the edge with no further clocking event; the sample
  // must not follow it.
  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev_data);

  f.scheduler.Run();

  // The live variable has moved to 0x3C...
  EXPECT_EQ(data->value.ToUint64(), 0x3Cu);

  // ...but reading the clockvar through EvalExpr yields the frozen sample 0xA5.
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kMemberAccess;
  member->lhs = f.arena.Create<Expr>();
  member->lhs->kind = ExprKind::kIdentifier;
  member->lhs->text = "cb";
  member->rhs = f.arena.Create<Expr>();
  member->rhs->kind = ExprKind::kIdentifier;
  member->rhs->text = "data";

  auto result = EvalExpr(member, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xA5u);
}

TEST(InputSamplingSim, SameSignalInMultipleBlocks) {
  ClockingSimFixture f;
  auto* clk1 = f.ctx.CreateVariable("clk1", 1);
  clk1->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* clk2 = f.ctx.CreateVariable("clk2", 1);
  clk2->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk1";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{0};
  block1.default_output_skew = SimTime{0};
  ClockingSignal sig1;
  sig1.signal_name = "data";
  sig1.direction = ClockingDir::kInput;
  block1.signals.push_back(sig1);
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cb2";
  block2.clock_signal = "clk2";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal sig2;
  sig2.signal_name = "data";
  sig2.direction = ClockingDir::kInput;
  block2.signals.push_back(sig2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk1, 10);

  auto* ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{15}, Region::kActive, ev_data);

  SchedulePosedge(f, clk2, 20);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb1", "data"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "data"), 0x22u);
}

TEST(InputSamplingSim, InoutSignalSampledAsInput) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x55u);
}

TEST(InputSamplingSim, SampledBeforeBlockEventFires) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x42);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  uint64_t value_seen_in_callback = 0;
  cmgr.RegisterEdgeCallback(
      "cb", f.ctx, f.scheduler, [&cmgr, &value_seen_in_callback]() {
        value_seen_in_callback = cmgr.GetSampledValue("cb", "data");
      });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(value_seen_in_callback, 0x42u);
}

// §14.13: the sampled-value rule covers inout clockvars as well as input ones
// -- reading an inout clockvar in an expression yields the value sampled at the
// most recent clocking event, just like an input clockvar. This exercises the
// inout branch of the sampler together with the real EvalExpr member-access
// read path (TryClockvarMemberAccess), the input form the input-direction
// frozen test does not cover.
TEST(InputSamplingSim, InoutClockvarReadYieldsSampledValue) {
  SimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x5A);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kMemberAccess;
  member->lhs = f.arena.Create<Expr>();
  member->lhs->kind = ExprKind::kIdentifier;
  member->lhs->text = "cb";
  member->rhs = f.arena.Create<Expr>();
  member->rhs->kind = ExprKind::kIdentifier;
  member->rhs->text = "data";

  auto result = EvalExpr(member, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x5Au);
}

}  // namespace
