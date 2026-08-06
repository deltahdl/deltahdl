#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";

// §39.4.2.1 (Claim A, rule): the deferred delivery tick is the nearest global
// clock tick strictly following the event. A tick that coincides with the event
// does not qualify, the smallest greater tick wins regardless of schedule
// order, and a schedule with no later tick yields the no-tick sentinel.
TEST(GlobalClockingFutureCallback, NearestTickIsStrictlyAfterTheEvent) {
  std::vector<uint64_t> ticks = {12, 10, 11};  // unsorted on purpose

  // The event at 11 defers to 12, not to the coinciding 11.
  EXPECT_EQ(AssertionApi::NearestGlobalClockTickAfter(ticks, 11), 12u);
  // The event at 10 defers to the next tick, 11.
  EXPECT_EQ(AssertionApi::NearestGlobalClockTickAfter(ticks, 10), 11u);
  // No tick follows an event past the last one.
  EXPECT_EQ(AssertionApi::NearestGlobalClockTickAfter(ticks, 12),
            AssertionApi::kNoGlobalClockTick);
}

// §39.4.2.1 (Claims A and B together — the LRM example): an assertion referring
// to a global clocking future sampled value function has its callback event at
// time 11 but its callback executes at the nearest later global clock tick, 12.
// At the event nothing fires; at the coinciding tick 11 still nothing fires;
// the callback runs only when the clock reaches 12 (Claim A). The cb_time
// delivered is 11 — the time of the event — not 12, while attemptStartTime
// stays 10 (Claim B).
TEST(GlobalClockingFutureCallback, DefersToNextTickButReportsEventTime) {
  AssertionApi api;
  api.SetGlobalClockTicks({10, 11, 12, 13});
  api.MarkAssertionUsesGlobalClockingFuture(kA);

  int fired = 0;
  uint64_t seen_cb_time = 0;
  uint64_t seen_attempt_start = 0;
  api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        ++fired;
        seen_cb_time = a.cb_time;
        if (a.info != nullptr) seen_attempt_start = a.info->attempt_start_time;
      },
      nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 10;

  // The event happens at time 11. The callback is deferred, not delivered.
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 11, info),
      0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);

  // Reaching the tick that coincides with the event (11) is not "strictly
  // following" — still nothing fires and the callback stays queued.
  EXPECT_EQ(api.AdvanceGlobalClockTick(11), 0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);

  // The nearest tick strictly following the event is 12: the callback executes.
  EXPECT_EQ(api.AdvanceGlobalClockTick(12), 1u);
  EXPECT_EQ(fired, 1);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 0u);

  // cb_time is the event time (11), not the delivery tick (12); the attempt
  // start time is unchanged (10).
  EXPECT_EQ(seen_cb_time, 11u);
  EXPECT_EQ(seen_attempt_start, 10u);
}

// §39.4.2.1 (scope guard): the deferral is specific to assertions referring to
// a global clocking future sampled value function. An assertion not so marked
// is delivered immediately at the event time through the same entry point, with
// cb_time equal to the event time and nothing left queued.
TEST(GlobalClockingFutureCallback, OrdinaryAssertionDeliversImmediately) {
  AssertionApi api;
  api.SetGlobalClockTicks({10, 11, 12});

  int fired = 0;
  uint64_t seen_cb_time = 0;
  api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        ++fired;
        seen_cb_time = a.cb_time;
      },
      nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 11;
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 11, info),
      1u);
  EXPECT_EQ(fired, 1);
  EXPECT_EQ(seen_cb_time, 11u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 0u);
}

// §39.4.2.1 (Claims A and B, multiple pending events — edge case): two events
// on a global-clocking-future assertion occur at different times and defer to
// different global clock ticks. Each callback must fire at its own nearest tick
// strictly following its event (Claim A), and each must report its own event
// time as cb_time (Claim B) — the deferral preserves the per-event time rather
// than collapsing to a single shared value. Advancing the clock to the first
// tick matures only the first; the second waits for its own later tick.
TEST(GlobalClockingFutureCallback, EachDeferredEventKeepsItsOwnTickAndTime) {
  AssertionApi api;
  api.SetGlobalClockTicks({10, 11, 12, 13, 14});
  api.MarkAssertionUsesGlobalClockingFuture(kA);

  std::vector<uint64_t> cb_times;
  std::vector<uint64_t> attempt_starts;
  api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        cb_times.push_back(a.cb_time);
        if (a.info != nullptr)
          attempt_starts.push_back(a.info->attempt_start_time);
      },
      nullptr);

  // First event at 11 (attempt started at 10) defers to tick 12.
  AssertionAttemptInfo first;
  first.attempt_start_time = 10;
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 11, first),
      0u);
  // Second event at 13 (attempt started at 12) defers to tick 14.
  AssertionAttemptInfo second;
  second.attempt_start_time = 12;
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 13, second),
      0u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 2u);

  // Reaching tick 12 matures only the first event; the second is not yet due.
  EXPECT_EQ(api.AdvanceGlobalClockTick(12), 1u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);
  ASSERT_EQ(cb_times.size(), 1u);
  EXPECT_EQ(cb_times[0], 11u);
  EXPECT_EQ(attempt_starts[0], 10u);

  // Reaching tick 14 matures the second event with its own event time.
  EXPECT_EQ(api.AdvanceGlobalClockTick(14), 1u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 0u);
  ASSERT_EQ(cb_times.size(), 2u);
  EXPECT_EQ(cb_times[1], 13u);
  EXPECT_EQ(attempt_starts[1], 12u);
}

// §39.4.2.1 (Claim A, edge case — no qualifying tick): the callback executes at
// the nearest global clock tick strictly following the event. When the event
// has no tick after it, there is no instant at which the deferred callback may
// run. The delivery machinery queues the callback but never matures it, however
// far the clock is advanced — "strictly following" admits no tick here, so none
// fires. This observes the no-tick sentinel propagating through the integrated
// deferral path, not just the standalone NearestGlobalClockTickAfter helper.
TEST(GlobalClockingFutureCallback, NoTickAfterEventNeverFires) {
  AssertionApi api;
  api.SetGlobalClockTicks({10, 11, 12});
  api.MarkAssertionUsesGlobalClockingFuture(kA);

  int fired = 0;
  api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&](const AssertionCallbackArgs&) { ++fired; }, nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 12;

  // The event coincides with the last tick (12); nothing strictly follows it,
  // so the callback is deferred (returns 0) rather than delivered now.
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 12, info),
      0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);

  // Advancing to the last scheduled tick and then well past it matures nothing:
  // no tick strictly follows the event, so the deferred callback stays queued.
  EXPECT_EQ(api.AdvanceGlobalClockTick(12), 0u);
  EXPECT_EQ(api.AdvanceGlobalClockTick(1000), 0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);
}

}  // namespace
