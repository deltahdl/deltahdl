#include <gtest/gtest.h>

#include <algorithm>
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

struct Timed {
  int reason = 0;
  uint64_t cb_time = 0;
  uint64_t now = 0;
  uint64_t attempt_start = 0;
  bool has_info = false;
  auto operator<=>(const Timed&) const = default;
};

std::vector<Timed> SortedCallsOf(const char* assertion) {
  std::vector<Timed> calls;
  for (const AssertionCall& call : AssertionCalls()) {
    if (call.assertion == assertion) {
      calls.push_back({call.reason, call.cb_time, call.now, call.attempt_start,
                       call.has_info});
    }
  }
  std::ranges::sort(calls);
  return calls;
}

std::vector<Timed> Sorted(std::vector<Timed> calls) {
  std::ranges::sort(calls);
  return calls;
}

void WatchEveryReasonOf(const char* assertion) {
  for (int reason : {cbAssertionStart, cbAssertionSuccess, cbAssertionFailure,
                     cbAssertionReset, cbAssertionDisable}) {
    ASSERT_NE(WatchAssertion(assertion, reason), nullptr);
  }
}

std::string GclkDesign(const std::string& assertions, const char* stimulus) {
  std::string src =
      "module top;\n"
      "  logic clk = 0, gclk = 0, a = 1, b = 1;\n"
      "  global clocking @(posedge gclk); endclocking\n"
      "  always #2 gclk = ~gclk;\n"
      "  always #4 clk = ~clk;\n";
  src += assertions;
  src += "  initial begin $arm; ";
  src += stimulus;
  src +=
      " end\n"
      "endmodule\n";
  return src;
}

struct FutureFunction {
  const char* name;
  bool holds_on_a_steady_one;
};

class GclkFutureRun : public AssertionRun,
                      public ::testing::WithParamInterface<FutureFunction> {
 protected:
  std::string Assertion() const {
    std::string assertion = "  af: assert property (@(posedge clk) ";
    assertion += GetParam().name;
    assertion += "(a)) else begin end\n";
    return assertion;
  }
};

INSTANTIATE_TEST_SUITE_P(
    EachFutureFunction, GclkFutureRun,
    ::testing::Values(FutureFunction{"$future_gclk", true},
                      FutureFunction{"$rising_gclk", false},
                      FutureFunction{"$falling_gclk", false},
                      FutureFunction{"$steady_gclk", true},
                      FutureFunction{"$changing_gclk", false}),
    [](const ::testing::TestParamInfo<FutureFunction>& info) {
      std::string name = info.param.name + 1;
      name.erase(name.size() - 5);
      return name;
    });

TEST_P(GclkFutureRun,
       DISABLED_AttemptCallbacksRunAtTheNextGlobalTickWithTheEventTime) {
  ArmInTurn({[] { WatchEveryReasonOf("top.af"); }});
  Run(GclkDesign(Assertion(), "#16 $finish;"));
  const int kVerdict = GetParam().holds_on_a_steady_one ? cbAssertionSuccess
                                                        : cbAssertionFailure;
  EXPECT_EQ(SortedCallsOf("top.af"),
            Sorted({{cbAssertionStart, 4, 6, 4, true},
                    {kVerdict, 4, 6, 4, true},
                    {cbAssertionStart, 12, 14, 12, true},
                    {kVerdict, 12, 14, 12, true}}));
}

TEST_P(GclkFutureRun, ControlCallbacksRunAtTheNextGlobalTickWithTheEventTime) {
  ArmInTurn({[] {
    for (int reason : {cbAssertionReset, cbAssertionDisable}) {
      ASSERT_NE(WatchAssertion("top.af", reason), nullptr);
    }
  }});
  Run(GclkDesign(Assertion(), "#5 $assertkill(0, top.af); #11 $finish;"));
  EXPECT_EQ(SortedCallsOf("top.af"),
            Sorted({{cbAssertionReset, 5, 6, 0, false},
                    {cbAssertionDisable, 5, 6, 0, false}}));
}

constexpr const char* kFigureAssertions =
    "  a1: assert property (@(posedge clk) $falling_gclk(a) |=> b)\n"
    "      else begin end\n"
    "  a2: assert property (@(posedge clk) a |=> $falling_gclk(b))\n"
    "      else begin end\n";

TEST_F(AssertionRun,
       DISABLED_AFutureFunctionInAnImplicationDefersItsAttemptCallbacks) {
  ArmInTurn({[] {
    WatchEveryReasonOf("top.a1");
    WatchEveryReasonOf("top.a2");
  }});
  Run(GclkDesign(kFigureAssertions, "#5 a = 0; #11 $finish;"));
  EXPECT_EQ(SortedCallsOf("top.a1"),
            Sorted({{cbAssertionStart, 4, 6, 4, true},
                    {cbAssertionSuccess, 12, 14, 4, true},
                    {cbAssertionStart, 12, 14, 12, true}}));
  EXPECT_EQ(SortedCallsOf("top.a2"),
            Sorted({{cbAssertionStart, 4, 6, 4, true},
                    {cbAssertionFailure, 12, 14, 4, true},
                    {cbAssertionStart, 12, 14, 12, true}}));
}

TEST_F(AssertionRun, AKillOfAFutureFunctionImplicationWaitsForTheTick) {
  ArmInTurn({[] {
    for (const char* assertion : {"top.a1", "top.a2"}) {
      for (int reason : {cbAssertionReset, cbAssertionDisable}) {
        ASSERT_NE(WatchAssertion(assertion, reason), nullptr);
      }
    }
  }});
  Run(GclkDesign(kFigureAssertions,
                 "#5 a = 0; #8 $assertkill(0, top.a1, top.a2); #3 $finish;"));
  for (const char* assertion : {"top.a1", "top.a2"}) {
    EXPECT_EQ(SortedCallsOf(assertion),
              Sorted({{cbAssertionReset, 13, 14, 0, false},
                      {cbAssertionDisable, 13, 14, 0, false}}))
        << assertion;
  }
}

}  // namespace
