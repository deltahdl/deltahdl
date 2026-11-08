#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "helpers_assertion_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";

TEST(GlobalClockingFutureCallback, NearestTickIsStrictlyAfterTheEvent) {
  std::vector<uint64_t> ticks = {12, 10, 11};

  EXPECT_EQ(AssertionApi::NearestGlobalClockTickAfter(ticks, 11), 12u);
  EXPECT_EQ(AssertionApi::NearestGlobalClockTickAfter(ticks, 10), 11u);
  EXPECT_EQ(AssertionApi::NearestGlobalClockTickAfter(ticks, 12),
            AssertionApi::kNoGlobalClockTick);
}

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

  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 11, info),
      0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);

  EXPECT_EQ(api.AdvanceGlobalClockTick(11), 0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);

  EXPECT_EQ(api.AdvanceGlobalClockTick(12), 1u);
  EXPECT_EQ(fired, 1);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 0u);

  EXPECT_EQ(seen_cb_time, 11u);
  EXPECT_EQ(seen_attempt_start, 10u);
}

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

  AssertionAttemptInfo first;
  first.attempt_start_time = 10;
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 11, first),
      0u);
  AssertionAttemptInfo second;
  second.attempt_start_time = 12;
  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 13, second),
      0u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 2u);

  EXPECT_EQ(api.AdvanceGlobalClockTick(12), 1u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);
  ASSERT_EQ(cb_times.size(), 1u);
  EXPECT_EQ(cb_times[0], 11u);
  EXPECT_EQ(attempt_starts[0], 10u);

  EXPECT_EQ(api.AdvanceGlobalClockTick(14), 1u);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 0u);
  ASSERT_EQ(cb_times.size(), 2u);
  EXPECT_EQ(cb_times[1], 13u);
  EXPECT_EQ(attempt_starts[1], 12u);
}

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

  EXPECT_EQ(
      api.DeliverAssertionEventAtGlobalClock(kA, cbAssertionStart, 12, info),
      0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);

  EXPECT_EQ(api.AdvanceGlobalClockTick(12), 0u);
  EXPECT_EQ(api.AdvanceGlobalClockTick(1000), 0u);
  EXPECT_EQ(fired, 0);
  EXPECT_EQ(api.PendingGlobalClockingCallbackCount(), 1u);
}

struct DeferredCall {
  PLI_INT32 reason = 0;
  PLI_UINT32 cb_time_low = 0;
  bool carried_info = false;
  PLI_UINT32 attempt_start_low = 0;
};

std::vector<DeferredCall> g_deferred_calls;

PLI_INT32 RecordDeferredCall(PLI_INT32 reason, s_vpi_time* cb_time, vpiHandle,
                             p_vpi_attempt_info info, PLI_BYTE8*) {
  DeferredCall call;
  call.reason = reason;
  call.cb_time_low = cb_time->low;
  call.carried_info = info != nullptr;
  if (info != nullptr) call.attempt_start_low = info->attemptStartTime.low;
  g_deferred_calls.push_back(call);
  return 0;
}

class GlobalClockingFutureCallbackEntry : public ::testing::Test {
 protected:
  void SetUp() override {
    g_deferred_calls.clear();
    SetGlobalVpiContext(&vpi_ctx_);
    SetGlobalAssertionApi(&api_);
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    SetGlobalVpiContext(nullptr);
  }

  VpiContext vpi_ctx_;
  AssertionApi api_;
};

TEST_F(GlobalClockingFutureCallbackEntry, TheRoutineIsHandedTheEventTime) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  api_.SetGlobalClockTicks({10, 11, 12, 13});
  api_.MarkAssertionUsesGlobalClockingFuture(kA);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionKill,
                                      &RecordDeferredCall, nullptr),
            nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 10;
  EXPECT_EQ(
      api_.DeliverAssertionEventAtGlobalClock(kA, cbAssertionKill, 11, info),
      0u);
  EXPECT_TRUE(g_deferred_calls.empty());

  EXPECT_EQ(api_.AdvanceGlobalClockTick(11), 0u);
  EXPECT_TRUE(g_deferred_calls.empty());

  EXPECT_EQ(api_.AdvanceGlobalClockTick(12), 1u);
  ASSERT_EQ(g_deferred_calls.size(), 1u);
  EXPECT_EQ(g_deferred_calls[0].reason, cbAssertionKill);
  EXPECT_EQ(g_deferred_calls[0].cb_time_low, 11u);
  EXPECT_FALSE(g_deferred_calls[0].carried_info);
}

TEST_F(GlobalClockingFutureCallbackEntry, TheDeferredCallKeepsItsAttempt) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  api_.SetGlobalClockTicks({10, 11, 12, 13});
  api_.MarkAssertionUsesGlobalClockingFuture(kA);
  ASSERT_NE(
      vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionFailure,
                                &RecordDeferredCall, nullptr),
      nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 10;
  info.fail_expr = "req && !ack";
  ASSERT_EQ(
      api_.DeliverAssertionEventAtGlobalClock(kA, cbAssertionFailure, 11, info),
      0u);
  ASSERT_EQ(api_.AdvanceGlobalClockTick(12), 1u);

  ASSERT_EQ(g_deferred_calls.size(), 1u);
  EXPECT_EQ(g_deferred_calls[0].reason, cbAssertionFailure);
  EXPECT_EQ(g_deferred_calls[0].cb_time_low, 11u);
  ASSERT_TRUE(g_deferred_calls[0].carried_info);
  EXPECT_EQ(g_deferred_calls[0].attempt_start_low, 10u);
}

TEST_F(AssertionRun, AControlCallbackOfAFutureGclkAssertionWaitsForTheTick) {
  AssertionArmer() = [] {
    for (const char* assertion : {"top.a1", "top.a2"}) {
      for (int reason : {cbAssertionReset, cbAssertionDisable}) {
        ASSERT_NE(WatchAssertion(assertion, reason), nullptr);
      }
    }
  };
  Run("module top;\n"
      "  logic clk = 0, gclk = 0, a = 1, b = 1;\n"
      "  global clocking @(posedge gclk); endclocking\n"
      "  a1: assert property (@(posedge clk) $falling_gclk(a))\n"
      "      else begin end\n"
      "  a2: assert property (@(posedge clk) a) else begin end\n"
      "  initial begin\n"
      "    $arm;\n"
      "    #10 clk = 1; gclk = 1;\n"
      "    #1 gclk = 0; $assertkill(0, top.a1, top.a2);\n"
      "    #1 gclk = 1;\n"
      "    #1 gclk = 0;\n"
      "  end\n"
      "endmodule\n");

  std::vector<AssertionCall> a1;
  std::vector<AssertionCall> a2;
  for (const AssertionCall& call : AssertionCalls()) {
    (call.assertion == "top.a1" ? a1 : a2).push_back(call);
  }
  ASSERT_EQ(a1.size(), 2u);
  ASSERT_EQ(a2.size(), 2u);
  for (const AssertionCall& call : a1) {
    EXPECT_EQ(call.cb_time, 11u);
    EXPECT_EQ(call.now, 12u);
  }
  for (const AssertionCall& call : a2) {
    EXPECT_EQ(call.cb_time, 11u);
    EXPECT_EQ(call.now, 11u);
  }
  EXPECT_EQ(a1[0].reason, cbAssertionReset);
  EXPECT_EQ(a1[1].reason, cbAssertionDisable);
}

}  // namespace
