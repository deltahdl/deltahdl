#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_coverage.h"

namespace delta {
namespace {

// §39.2 "Overview" says what the assertion capabilities are for, as four things
// they enable: a user's C code to react to assertion events, and third-party
// assertion "waveform" dumping, coverage, and debug tools to be written. It
// sets out no rule of its own - each capability is carried by machinery a later
// subclause defines - so what it claims is that everything such an application
// needs is reachable. These tests take the four one at a time and write the
// small end of each application against this tool.

// The event trace a dumping tool keeps: what happened, to which assertion,
// when, and which attempt of it. §39.4.2 makes the attempt's start time what
// "uniquely identifies it among the attempts of an assertion", which is what
// lets a dump keep two overlapping attempts apart.
struct DumpedEvent {
  int reason = 0;
  vpiHandle assertion = nullptr;
  PLI_UINT32 time_low = 0;
  PLI_UINT32 attempt_low = 0;
};

std::vector<DumpedEvent> g_dump;

PLI_INT32 DumpAssertionEvent(PLI_INT32 reason, s_vpi_time* cb_time,
                             vpiHandle assertion, p_vpi_attempt_info info,
                             PLI_BYTE8* user_data) {
  DumpedEvent event;
  event.reason = reason;
  event.assertion = assertion;
  event.time_low = cb_time->low;
  if (info != nullptr) event.attempt_low = info->attempt_start_time.low;
  static_cast<void>(user_data);
  g_dump.push_back(event);
  return 0;
}

class AssertionCapabilities : public ::testing::Test {
 protected:
  void SetUp() override {
    g_dump.clear();
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

// §39.2, first capability: "a user's C code to react to assertion events". The
// C code is a routine of the application's own, the event is one the assertion
// raised, and reacting to it is the routine running with the event in hand -
// which assertion, which reason, and at what time.
TEST_F(AssertionCapabilities, UserCCodeReactsToAnAssertionEvent) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionFailure,
                                      &DumpAssertionEvent, nullptr),
            nullptr);

  AssertionAttemptInfo attempt;
  attempt.attempt_start_time = 10;
  attempt.fail_expr = "req && !ack";
  EXPECT_EQ(api_.DeliverAssertionEvent("handshake_p", cbAssertionFailure, 14,
                                       attempt),
            1u);

  ASSERT_EQ(g_dump.size(), 1u);
  EXPECT_EQ(g_dump[0].reason, cbAssertionFailure);
  EXPECT_EQ(g_dump[0].assertion, assertion);
  EXPECT_EQ(g_dump[0].time_low, 14u);
}

// §39.2, second capability: an assertion "waveform" dumping tool. A dump is a
// sequence of events in time, and the events of one assertion's overlapping
// attempts have to land on the right attempt: §39.4.2 makes the attempt's start
// time what identifies it, and the callback carries it with every event. Two
// attempts start here before either finishes, and the trace keeps them apart.
TEST_F(AssertionCapabilities, WaveformDumpingSeparatesOverlappingAttempts) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionStart,
                                      &DumpAssertionEvent, nullptr),
            nullptr);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionSuccess,
                                      &DumpAssertionEvent, nullptr),
            nullptr);

  AssertionAttemptInfo first;
  first.attempt_start_time = 10;
  AssertionAttemptInfo second;
  second.attempt_start_time = 20;
  api_.DeliverAssertionEvent("handshake_p", cbAssertionStart, 10, first);
  api_.DeliverAssertionEvent("handshake_p", cbAssertionStart, 20, second);
  api_.DeliverAssertionEvent("handshake_p", cbAssertionSuccess, 30, first);
  api_.DeliverAssertionEvent("handshake_p", cbAssertionSuccess, 40, second);

  ASSERT_EQ(g_dump.size(), 4u);
  // The success at 30 belongs to the attempt that started at 10, and the one at
  // 40 to the attempt that started at 20, which is what a dump draws.
  EXPECT_EQ(g_dump[2].time_low, 30u);
  EXPECT_EQ(g_dump[2].attempt_low, 10u);
  EXPECT_EQ(g_dump[3].time_low, 40u);
  EXPECT_EQ(g_dump[3].attempt_low, 20u);
}

// §39.2, third capability: an assertion coverage tool. Such a tool asks what an
// assertion did over the run - how many attempts it made and how each of them
// came out - and asks an instance how many of its assertions were covered at
// all. Both answer from the tallies the coverage properties read (§40.5).
TEST_F(AssertionCapabilities, CoverageToolsReadTheAssertionTallies) {
  AssertionCoverageCounters counters;
  counters.attempts = 7;
  counters.successes = 4;
  counters.vacuous_successes = 1;
  counters.failures = 1;
  counters.killed = 1;

  EXPECT_EQ(
      AssertionStatusQuery(CoverageProperty::kAssertAttemptCovered, counters),
      7u);
  EXPECT_EQ(
      AssertionStatusQuery(CoverageProperty::kAssertSuccessCovered, counters),
      4u);
  EXPECT_EQ(
      AssertionStatusQuery(CoverageProperty::kAssertFailureCovered, counters),
      1u);

  InstanceCoverage instance;
  instance.assertions.total = 3;
  instance.assertions.covered = 2;
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kAssertCoverage, instance),
            2u);
}

// §39.2, fourth capability: an assertion debug tool. Debugging an assertion
// means following an attempt through it rather than only learning that it
// failed, which is what §39.4.2's step callbacks carry: the expressions matched
// on the way and the state the step went from and to, with the last expression
// of a failing step being where the transition failed. The step detail is
// delivered in the model's own terms - the source text of each expression - so
// this is where a debug tool reads it; the C structure of §39.4.2 carries those
// expressions as handles, which this tool has none of until a run's assertion
// engine drives the API (see src/simulator/vpi_assertion_cb.cpp).
TEST_F(AssertionCapabilities, DebugToolsFollowAnAttemptStepByStep) {
  std::vector<AssertionStepDetail> steps;
  api_.PlaceAssertionCallback(
      cbAssertionStepSuccess, "handshake_p", vpiAssert,
      [&steps](const AssertionCallbackArgs& args) {
        if (args.info != nullptr) steps.push_back(args.info->step);
      },
      nullptr);

  AssertionAttemptInfo matched;
  matched.attempt_start_time = 10;
  matched.step.matched_exprs = {"req"};
  matched.step.state_from = 0;
  matched.step.state_to = 2;
  api_.DeliverAssertionEvent("handshake_p", cbAssertionStepSuccess, 12,
                             matched);

  AssertionAttemptInfo failed;
  failed.attempt_start_time = 10;
  failed.step.matched_exprs = {"req", "ack"};
  failed.step.state_from = 2;
  failed.step.state_to = 1;
  api_.DeliverAssertionEvent("handshake_p", cbAssertionStepFailure, 13, failed);

  ASSERT_EQ(steps.size(), 2u);
  EXPECT_EQ(steps[0].state_from, 0);
  EXPECT_EQ(steps[0].state_to, 2);
  EXPECT_EQ(steps[1].state_from, 2);
  // §39.4.2: on a failing transition the last expression in the array is the
  // one where the transition failed, so a debug tool has the place to point at.
  ASSERT_EQ(steps[1].matched_exprs.size(), 2u);
  EXPECT_EQ(steps[1].matched_exprs.back(), "ack");
}

}  // namespace
}  // namespace delta
