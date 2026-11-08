#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

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
  if (info != nullptr) event.attempt_low = info->attemptStartTime.low;
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

TEST_F(AssertionCapabilities, UserCCodeReactsToAnAssertionEvent) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  ASSERT_NE(
      vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionFailure,
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
  EXPECT_EQ(VpiObjectOf(g_dump[0].assertion), assertion);
  EXPECT_EQ(g_dump[0].time_low, 14u);
}

TEST_F(AssertionCapabilities, WaveformDumpingSeparatesOverlappingAttempts) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionStart,
                                      &DumpAssertionEvent, nullptr),
            nullptr);
  ASSERT_NE(
      vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionSuccess,
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
  EXPECT_EQ(g_dump[2].time_low, 30u);
  EXPECT_EQ(g_dump[2].attempt_low, 10u);
  EXPECT_EQ(g_dump[3].time_low, 40u);
  EXPECT_EQ(g_dump[3].attempt_low, 20u);
}

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
  ASSERT_EQ(steps[1].matched_exprs.size(), 2u);
  EXPECT_EQ(steps[1].matched_exprs.back(), "ack");
}

}  // namespace
}  // namespace delta
