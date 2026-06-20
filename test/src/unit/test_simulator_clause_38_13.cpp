#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiGetTimeSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Advance the simulation clock to `t` by draining a no-op event scheduled
  // there; after Run() the scheduler's current time is that slot.
  void AdvanceTo(uint64_t t) {
    auto* ev = scheduler_.GetEventPool().Acquire();
    ev->callback = []() {};
    scheduler_.ScheduleEvent(SimTime{t}, Region::kActive, ev);
    scheduler_.Run();
  }

  // Leave a future event pending at `t` without running, so the current time is
  // unchanged but the next-future-event time is `t`.
  void SchedulePendingAt(uint64_t t) {
    auto* ev = scheduler_.GetEventPool().Acquire();
    ev->callback = []() {};
    scheduler_.ScheduleEvent(SimTime{t}, Region::kActive, ev);
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §38.13 shall #1 + Syntax (Figure 38-6): vpi_get_time() retrieves the current
// simulation time; a vpiSimTime result is the full 64-bit count split across
// the high and low 32-bit halves.
TEST_F(VpiGetTimeSim, SimTimeSplitsAcrossHighAndLow) {
  const uint64_t kTicks = (static_cast<uint64_t>(3) << 32) | 5u;
  AdvanceTo(kTicks);

  s_vpi_time out = {};
  out.type = vpiSimTime;
  vpi_get_time(nullptr, &out);

  EXPECT_EQ(out.high, 3u);
  EXPECT_EQ(out.low, 5u);
}

// §38.13 shall #2: the caller's time_p->type chooses the form of the result.
// At the same instant, vpiSimTime fills high/low while vpiScaledRealTime fills
// real.
TEST_F(VpiGetTimeSim, TypeFieldSelectsSimVersusScaledReal) {
  AdvanceTo(7);

  s_vpi_time as_sim = {};
  as_sim.type = vpiSimTime;
  vpi_get_time(nullptr, &as_sim);
  EXPECT_EQ(as_sim.low, 7u);
  EXPECT_DOUBLE_EQ(as_sim.real, 0.0);

  s_vpi_time as_real = {};
  as_real.type = vpiScaledRealTime;
  vpi_get_time(nullptr, &as_real);
  EXPECT_DOUBLE_EQ(as_real.real, 7.0);
  EXPECT_EQ(as_real.low, 0u);
}

// §38.13 shall #1: a scaled-real result uses the timescale of the object. With
// the simulation counting in picoseconds and the object's unit a nanosecond,
// 1000 ps reads back as 1.0 in the object's unit.
TEST_F(VpiGetTimeSim, ScaledRealUsesObjectTimescale) {
  vpi_ctx_.SetSimTimeUnit(-12);  // simulation counts in 1 ps
  AdvanceTo(1000);

  vpiHandle obj = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(obj, nullptr);
  obj->time_unit = -9;  // object's timescale is 1 ns

  s_vpi_time out = {};
  out.type = vpiScaledRealTime;
  vpi_get_time(obj, &out);

  EXPECT_DOUBLE_EQ(out.real, 1.0);
}

// §38.13 D1: when obj is null the time is retrieved using the simulation time
// unit, so no per-object scaling is applied and the scaled real equals the raw
// picosecond count.
TEST_F(VpiGetTimeSim, NullObjectUsesSimulationTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);  // simulation counts in 1 ps
  AdvanceTo(1000);

  s_vpi_time out = {};
  out.type = vpiScaledRealTime;
  vpi_get_time(nullptr, &out);

  EXPECT_DOUBLE_EQ(out.real, 1000.0);
}

// §38.13 D2: a time queue object reports the scheduled time of the next future
// event, not the current time. With current time 0 and an event pending at 50,
// the time queue reads 50 while a current-time query reads 0.
TEST_F(VpiGetTimeSim, TimeQueueReportsNextFutureEvent) {
  SchedulePendingAt(50);  // pending future event; current time stays 0

  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  EXPECT_EQ(now.low, 0u);

  vpiHandle tq = vpi_ctx_.CreateTimeQueue();
  ASSERT_NE(tq, nullptr);

  s_vpi_time future = {};
  future.type = vpiSimTime;
  vpi_get_time(tq, &future);
  EXPECT_EQ(future.low, 50u);
}

// §38.13 D2: a time queue object is read in the simulation time unit, so its
// scaled-real result is not scaled by any object timescale.
TEST_F(VpiGetTimeSim, TimeQueueUsesSimulationTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);
  SchedulePendingAt(1000);

  vpiHandle tq = vpi_ctx_.CreateTimeQueue();
  ASSERT_NE(tq, nullptr);

  s_vpi_time out = {};
  out.type = vpiScaledRealTime;
  vpi_get_time(tq, &out);

  EXPECT_DOUBLE_EQ(out.real, 1000.0);
}

// §38.13 shall #3: the destination memory belongs to the application. The
// routine fills a caller-owned structure in place rather than allocating one,
// so the caller's local keeps its address and receives the data.
TEST_F(VpiGetTimeSim, WritesIntoApplicationAllocatedMemory) {
  AdvanceTo(9);

  s_vpi_time caller_owned = {};
  caller_owned.type = vpiSimTime;
  s_vpi_time* before = &caller_owned;
  vpi_get_time(nullptr, &caller_owned);

  EXPECT_EQ(before, &caller_owned);
  EXPECT_EQ(caller_owned.low, 9u);
}

// §38.13 / §38.1: the destination is mandatory. With no structure to fill there
// is nothing to do, and the call must be safe.
TEST_F(VpiGetTimeSim, NullDestinationIsSafe) {
  AdvanceTo(3);
  vpi_get_time(nullptr, nullptr);
  SUCCEED();
}

}  // namespace
}  // namespace delta
