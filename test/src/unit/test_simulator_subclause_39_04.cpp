#include <gtest/gtest.h>

#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_assertion_cb.h"

namespace delta {
namespace {

// §39.4 "Dynamic information" says what the subclause is for in one sentence:
// "This subclause defines how to place assertion system and assertion
// callbacks." Two kinds of callback, two ways of placing them - §39.4.1 places
// a system callback with vpi_register_cb() and a reason naming something the
// assertion system as a whole did, §39.4.2 places an assertion callback with
// vpi_register_assertion_cb() on one assertion - and the information they carry
// is dynamic, which is what puts this subclause opposite §39.3's static list.
// These tests place one of each and watch the two stay apart, and then watch
// what a placed callback reports move as the run moves.

int g_system_calls = 0;

int RecordSystemCallback(VpiCbData*) {
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

// §39.4: the two kinds of callback are placed by their own routines and answer
// to their own events. A system reason reaches the callback placed for the
// system and leaves the one placed on an assertion alone; an event on that
// assertion does the reverse. Placing both and raising one at a time is what
// tells them apart.
TEST_F(AssertionDynamicInformation, TheSystemAndAssertionCallbacksStayApart) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  s_cb_data system_cb = {};
  system_cb.reason = cbAssertionSysOff;
  system_cb.cb_rtn = &RecordSystemCallback;
  ASSERT_NE(vpi_register_cb(&system_cb), nullptr);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionStart,
                                      &RecordAssertionEvent, nullptr),
            nullptr);

  // The assertion system was turned off: the system callback runs, and the
  // callback placed on the assertion has nothing to do with it.
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysOff), 1);
  EXPECT_EQ(g_system_calls, 1);
  EXPECT_TRUE(g_assertion_events.empty());

  // An attempt of the assertion started: the callback placed on it runs, and
  // the system callback is not what that event is delivered to.
  AssertionAttemptInfo attempt;
  attempt.attempt_start_time = 10;
  EXPECT_EQ(
      api_.DeliverAssertionEvent("handshake_p", cbAssertionStart, 10, attempt),
      1u);
  EXPECT_EQ(g_assertion_events.size(), 1u);
  EXPECT_EQ(g_system_calls, 1);
}

// §39.4: what these callbacks carry is dynamic information - it is about what
// the assertion is doing now rather than about how it was written, so the same
// routine on the same assertion reports something different each time the run
// reaches it. Here one placement sees an attempt start, fail, and be killed,
// each at its own time.
TEST_F(AssertionDynamicInformation, WhatAPlacedCallbackReportsMovesWithTheRun) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionStart,
                                      &RecordAssertionEvent, nullptr),
            nullptr);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionFailure,
                                      &RecordAssertionEvent, nullptr),
            nullptr);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionKill,
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
