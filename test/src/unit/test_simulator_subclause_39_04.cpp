#include <gtest/gtest.h>

#include <vector>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_system_calls = 0;

int RecordSystemCallback(s_cb_data*) {
  ++g_system_calls;
  return 0;
}

struct AssertionEventSeen {
  PLI_INT32 reason = 0;
  PLI_UINT32 time_low = 0;
};

std::vector<AssertionEventSeen> g_assertion_events;

PLI_INT32 RecordAssertionEvent(PLI_INT32 reason, s_vpi_time* cb_time, vpiHandle,
                               p_vpi_attempt_info, PLI_BYTE8*) {
  AssertionEventSeen seen;
  seen.reason = reason;
  seen.time_low = cb_time->low;
  g_assertion_events.push_back(seen);
  return 0;
}

class AssertionDynamicInformation : public ::testing::Test {
 protected:
  void SetUp() override {
    g_system_calls = 0;
    g_assertion_events.clear();
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

TEST_F(AssertionDynamicInformation, TheSystemAndAssertionCallbacksStayApart) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  s_cb_data system_cb = {};
  system_cb.reason = cbAssertionSysOff;
  system_cb.cb_rtn = &RecordSystemCallback;
  ASSERT_NE(vpi_register_cb(&system_cb), nullptr);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionStart,
                                      &RecordAssertionEvent, nullptr),
            nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysOff), 1);
  EXPECT_EQ(g_system_calls, 1);
  EXPECT_TRUE(g_assertion_events.empty());

  AssertionAttemptInfo attempt;
  attempt.attempt_start_time = 10;
  EXPECT_EQ(
      api_.DeliverAssertionEvent("handshake_p", cbAssertionStart, 10, attempt),
      1u);
  EXPECT_EQ(g_assertion_events.size(), 1u);
  EXPECT_EQ(g_system_calls, 1);
}

TEST_F(AssertionDynamicInformation, WhatAPlacedCallbackReportsMovesWithTheRun) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionStart,
                                      &RecordAssertionEvent, nullptr),
            nullptr);
  ASSERT_NE(
      vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionFailure,
                                &RecordAssertionEvent, nullptr),
      nullptr);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionKill,
                                      &RecordAssertionEvent, nullptr),
            nullptr);

  AssertionAttemptInfo attempt;
  attempt.attempt_start_time = 10;
  api_.DeliverAssertionEvent("handshake_p", cbAssertionStart, 10, attempt);
  attempt.fail_expr = "req && !ack";
  api_.DeliverAssertionEvent("handshake_p", cbAssertionFailure, 14, attempt);
  api_.DeliverAssertionEvent("handshake_p", cbAssertionKill, 20, attempt);

  ASSERT_EQ(g_assertion_events.size(), 3u);
  EXPECT_EQ(g_assertion_events[0].reason, cbAssertionStart);
  EXPECT_EQ(g_assertion_events[0].time_low, 10u);
  EXPECT_EQ(g_assertion_events[1].reason, cbAssertionFailure);
  EXPECT_EQ(g_assertion_events[1].time_low, 14u);
  EXPECT_EQ(g_assertion_events[2].reason, cbAssertionKill);
  EXPECT_EQ(g_assertion_events[2].time_low, 20u);
}

}  // namespace
}  // namespace delta
