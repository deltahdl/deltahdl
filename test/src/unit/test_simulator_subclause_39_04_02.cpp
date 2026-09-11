#include <gtest/gtest.h>

#include <iterator>
#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_assertion_cb.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";
constexpr const char* kB = "top.a2";

auto noop_cb = [](const AssertionCallbackArgs&) {};

// §39.4.2: the assertion callback reasons are all defined, distinct, and
// recognized as assertion callback reasons.
TEST(AssertionCallback, ReasonConstantsDefinedAndDistinct) {
  int reasons[] = {cbAssertionStart,
                   cbAssertionSuccess,
                   cbAssertionVacuousSuccess,
                   cbAssertionDisabledEvaluation,
                   cbAssertionFailure,
                   cbAssertionStepSuccess,
                   cbAssertionStepFailure,
                   cbAssertionLock,
                   cbAssertionUnlock,
                   cbAssertionDisable,
                   cbAssertionEnable,
                   cbAssertionReset,
                   cbAssertionKill,
                   cbAssertionDisablePassAction,
                   cbAssertionEnablePassAction,
                   cbAssertionDisableFailAction,
                   cbAssertionEnableFailAction,
                   cbAssertionDisableVacuousAction,
                   cbAssertionEnableNonvacuousAction};
  for (size_t i = 0; i < std::size(reasons); ++i) {
    EXPECT_TRUE(AssertionApi::IsAssertionCallbackReason(reasons[i]));
    for (size_t j = i + 1; j < std::size(reasons); ++j) {
      EXPECT_NE(reasons[i], reasons[j]);
    }
  }
  // A constant from a different subclause is not an assertion callback reason.
  EXPECT_FALSE(AssertionApi::IsAssertionCallbackReason(vpiAssertionSysOff));
}

// §39.4.2: the registration prototype, callback typedef, and the attempt/step
// information structures exist with the described shape. A null assertion
// handle is an error, so the registration entry point returns a NULL handle.
TEST(AssertionCallback, ApiSurfaceMatchesPrototype) {
  s_vpi_assertion_step_info step{};
  step.matched_expression_count = 0;
  step.matched_exprs = nullptr;
  step.state_from = 0;
  step.state_to = 1;

  s_vpi_attempt_info info{};
  info.detail.step = &step;
  (void)info.attempt_start_time;

  vpi_assertion_callback_func fn = nullptr;
  (void)fn;

  vpiHandle h =
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

// §39.4.2: a successful placement returns a non-null handle; that handle
// removes the callback (modeling vpi_remove_cb). An empty (invalid) handle
// errors.
TEST(AssertionCallback, PlaceReturnsHandleAndRemovesByHandle) {
  AssertionApi api;
  AssertionCallbackHandle h = api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert, noop_cb, nullptr);
  EXPECT_NE(h, 0u);
  EXPECT_EQ(api.PlacedCallbackCount(), 1u);

  EXPECT_TRUE(api.RemoveAssertionCallback(h));
  EXPECT_EQ(api.PlacedCallbackCount(), 0u);
  // Removing an already-removed handle reports no removal.
  EXPECT_FALSE(api.RemoveAssertionCallback(h));

  // An empty handle is an error: the NULL handle is returned.
  EXPECT_EQ(api.PlaceAssertionCallback(cbAssertionStart, "", vpiAssert, noop_cb,
                                       nullptr),
            0u);
}

// §39.4.2: an unrecognized reason cannot be placed; the NULL handle is
// returned.
TEST(AssertionCallback, UnknownReasonErrorsWithNullHandle) {
  AssertionApi api;
  EXPECT_EQ(api.PlaceAssertionCallback(vpiAssertionSysOff, kA, vpiAssert,
                                       noop_cb, nullptr),
            0u);
  EXPECT_EQ(api.PlacedCallbackCount(), 0u);
}

// §39.4.2: every reason may be placed on a concurrent or immediate assertion;
// only start, success, and failure may also be placed on a sequence or property
// instance; no other handle type bears assertion callbacks.
TEST(AssertionCallback, HandleTypeValidity) {
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionDisable, vpiAssert));
  EXPECT_TRUE(AssertionApi::IsReasonValidForHandle(cbAssertionStepSuccess,
                                                   vpiImmediateAssert));
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionStart, vpiSequenceDecl));
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionSuccess, vpiProperty));
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionFailure, vpiProperty));

  // Reasons other than start/success/failure are not valid on a sequence or
  // property instance.
  EXPECT_FALSE(AssertionApi::IsReasonValidForHandle(cbAssertionDisable,
                                                    vpiSequenceDecl));
  EXPECT_FALSE(AssertionApi::IsReasonValidForHandle(cbAssertionStepSuccess,
                                                    vpiProperty));
  // A non-assertion handle accepts no assertion callbacks.
  EXPECT_FALSE(
      AssertionApi::IsReasonValidForHandle(cbAssertionStart, vpiModule));
}

// §39.4.2: placing a reason that is invalid for the handle type is rejected
// with the NULL handle.
TEST(AssertionCallback, PlaceRejectsReasonInvalidForHandle) {
  AssertionApi api;
  EXPECT_EQ(api.PlaceAssertionCallback(cbAssertionDisable, kA, vpiSequenceDecl,
                                       noop_cb, nullptr),
            0u);
  // The same reason is accepted on a concurrent assertion statement.
  EXPECT_NE(api.PlaceAssertionCallback(cbAssertionDisable, kA, vpiAssert,
                                       noop_cb, nullptr),
            0u);
}

// §39.4.2 (handle-validity, first sentence): every assertion callback reason
// may be placed on any concurrent OR immediate assertion statement — that is,
// on an assert, assume, or cover, whether immediate or concurrent, not only on
// the assert form the other tests exercise. Each admitted statement handle type
// is a distinct accepting input; every one yields a valid (non-null) placement.
TEST(AssertionCallback, PlacesOnEveryAssertionStatementHandleType) {
  int handle_types[] = {vpiAssert,          vpiAssume,
                        vpiCover,           vpiImmediateAssert,
                        vpiImmediateAssume, vpiImmediateCover};
  for (int handle_type : handle_types) {
    AssertionApi api;
    // A control-only reason (never valid on a sequence/property instance)
    // confirms it is the statement-handle acceptance, not a start/success/
    // failure carve-out, that admits the placement.
    EXPECT_NE(api.PlaceAssertionCallback(cbAssertionKill, kA, handle_type,
                                         noop_cb, nullptr),
              0u);
    EXPECT_EQ(api.PlacedCallbackCount(), 1u);
  }
}

// §39.4.2: the callback is specific to the assertion it was placed on (events
// on a different assertion do not trigger it), and it continues to be called
// each time the event occurs until it is removed.
TEST(AssertionCallback, FiresPerAssertionUntilRemoved) {
  AssertionApi api;
  int count = 0;
  AssertionCallbackHandle h = api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&count](const AssertionCallbackArgs&) { ++count; }, nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 10;

  // An event on a different assertion does not trigger this callback.
  api.DeliverAssertionEvent(kB, cbAssertionStart, 10, info);
  EXPECT_EQ(count, 0);

  // Repeated events on its own assertion call it each time.
  api.DeliverAssertionEvent(kA, cbAssertionStart, 10, info);
  api.DeliverAssertionEvent(kA, cbAssertionStart, 12, info);
  EXPECT_EQ(count, 2);

  // Once removed it is no longer called.
  api.RemoveAssertionCallback(h);
  api.DeliverAssertionEvent(kA, cbAssertionStart, 14, info);
  EXPECT_EQ(count, 2);
}

// §39.4.2: the callback is supplied the reason, the callback time, the
// assertion handle, the attempt-info pointer, and the registered user data.
// attemptStart- Time is the start time of the actual attempt.
TEST(AssertionCallback, SuppliesFiveArguments) {
  AssertionApi api;
  int reason = 0;
  uint64_t cb_time = 0;
  std::string assertion;
  uint64_t attempt_start = 0;
  void* seen_user = nullptr;
  int user = 7;

  api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        reason = a.reason;
        cb_time = a.cb_time;
        assertion = a.assertion;
        seen_user = a.user_data;
        if (a.info != nullptr) attempt_start = a.info->attempt_start_time;
      },
      &user);

  AssertionAttemptInfo info;
  info.attempt_start_time = 42;
  api.DeliverAssertionEvent(kA, cbAssertionStart, 42, info);

  EXPECT_EQ(reason, cbAssertionStart);
  EXPECT_EQ(cb_time, 42u);
  EXPECT_EQ(assertion, kA);
  EXPECT_EQ(attempt_start, 42u);
  EXPECT_EQ(seen_user, &user);
}

// §39.4.2: classification of which reasons carry attempt information. The
// control and action callbacks carry none; the attempt-outcome and step
// callbacks do.
TEST(AssertionCallback, ReasonCarriesAttemptInfoClassification) {
  int no_info[] = {cbAssertionLock,
                   cbAssertionUnlock,
                   cbAssertionDisable,
                   cbAssertionEnable,
                   cbAssertionReset,
                   cbAssertionKill,
                   cbAssertionDisablePassAction,
                   cbAssertionEnablePassAction,
                   cbAssertionDisableFailAction,
                   cbAssertionEnableFailAction,
                   cbAssertionDisableVacuousAction,
                   cbAssertionEnableNonvacuousAction};
  for (int r : no_info) {
    EXPECT_FALSE(AssertionApi::ReasonCarriesAttemptInfo(r));
  }

  int has_info[] = {cbAssertionStart,
                    cbAssertionSuccess,
                    cbAssertionFailure,
                    cbAssertionStepSuccess,
                    cbAssertionStepFailure,
                    cbAssertionVacuousSuccess,
                    cbAssertionDisabledEvaluation};
  for (int r : has_info) {
    EXPECT_TRUE(AssertionApi::ReasonCarriesAttemptInfo(r));
  }
}

// §39.4.2: on a control/action callback the attempt-info pointer delivered to
// the callback is null.
TEST(AssertionCallback, ControlReasonDeliversNullAttemptInfo) {
  AssertionApi api;
  bool had_info = true;
  api.PlaceAssertionCallback(
      cbAssertionDisable, kA, vpiAssert,
      [&had_info](const AssertionCallbackArgs& a) {
        had_info = (a.info != nullptr);
      },
      nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 10;
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionDisable, 10, info), 1u);
  EXPECT_FALSE(had_info);
}

// §39.4.2: on a failure callback the attemptStartTime and detail.failExpr are
// valid.
TEST(AssertionCallback, FailureDeliversFailExpr) {
  AssertionApi api;
  std::string fail_expr;
  uint64_t attempt_start = 0;
  api.PlaceAssertionCallback(
      cbAssertionFailure, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        if (a.info != nullptr) {
          fail_expr = a.info->fail_expr;
          attempt_start = a.info->attempt_start_time;
        }
      },
      nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 5;
  info.fail_expr = "a && b";
  api.DeliverAssertionEvent(kA, cbAssertionFailure, 5, info);

  EXPECT_EQ(fail_expr, "a && b");
  EXPECT_EQ(attempt_start, 5u);
}

// §39.4.2 (handle-validity, second sentence): a failure callback placed on a
// property instance — not only a concurrent/immediate assertion statement — is
// a valid placement that actually fires and delivers its attempt information.
// Every other delivery test uses an assertion-statement handle; this observes
// that the property-instance placement branch yields a live, firing callback.
TEST(AssertionCallback, FailureCallbackFiresWhenPlacedOnPropertyInstance) {
  AssertionApi api;
  int count = 0;
  std::string fail_expr;
  uint64_t attempt_start = 0;
  AssertionCallbackHandle h = api.PlaceAssertionCallback(
      cbAssertionFailure, kA, vpiProperty,
      [&](const AssertionCallbackArgs& a) {
        ++count;
        if (a.info != nullptr) {
          fail_expr = a.info->fail_expr;
          attempt_start = a.info->attempt_start_time;
        }
      },
      nullptr);
  // The property-instance placement succeeds (non-null handle).
  EXPECT_NE(h, 0u);

  AssertionAttemptInfo info;
  info.attempt_start_time = 8;
  info.fail_expr = "req && !gnt";
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionFailure, 8, info), 1u);

  EXPECT_EQ(count, 1);
  EXPECT_EQ(fail_expr, "req && !gnt");
  EXPECT_EQ(attempt_start, 8u);
}

// §39.4.2: a placed step callback is invoked for both success and failure
// steps, and the step exposes the source/destination states and matched
// expressions. An empty expression set models an unconditional transition.
TEST(AssertionCallback, StepCallbackFiresForSuccessAndFailure) {
  AssertionApi api;
  int count = 0;
  int last_from = -1;
  int last_to = -1;
  size_t last_exprs = 99;
  api.PlaceAssertionCallback(
      cbAssertionStepSuccess, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        ++count;
        if (a.info != nullptr) {
          last_from = a.info->step.state_from;
          last_to = a.info->step.state_to;
          last_exprs = a.info->step.matched_exprs.size();
        }
      },
      nullptr);

  // A successful, unconditional transition (zero expressions).
  AssertionAttemptInfo success;
  success.step.state_from = 0;
  success.step.state_to = 2;
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepSuccess, 10, success),
            1u);
  EXPECT_EQ(count, 1);
  EXPECT_EQ(last_from, 0);
  EXPECT_EQ(last_to, 2);
  EXPECT_EQ(last_exprs, 0u);

  // The same callback also fires on a failure step (state_to 1 is accepting).
  AssertionAttemptInfo failure;
  failure.step.state_from = 2;
  failure.step.state_to = 1;
  failure.step.matched_exprs = {"x"};
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepFailure, 11, failure),
            1u);
  EXPECT_EQ(count, 2);
  EXPECT_EQ(last_exprs, 1u);
}

// §39.4.2 detail a): in a failing transition there shall always be at least one
// element in the expression array. A malformed failing step is rejected by the
// validator and fires no callback.
TEST(AssertionCallback, FailingStepRequiresAtLeastOneExpression) {
  AssertionStepDetail empty;
  EXPECT_FALSE(AssertionApi::IsValidFailingStep(empty));
  AssertionStepDetail one;
  one.matched_exprs = {"e"};
  EXPECT_TRUE(AssertionApi::IsValidFailingStep(one));

  AssertionApi api;
  int count = 0;
  api.PlaceAssertionCallback(
      cbAssertionStepFailure, kA, vpiAssert,
      [&count](const AssertionCallbackArgs&) { ++count; }, nullptr);

  AssertionAttemptInfo bad;  // failing step with no expressions
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepFailure, 10, bad), 0u);
  EXPECT_EQ(count, 0);

  AssertionAttemptInfo good;
  good.step.matched_exprs = {"e"};
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepFailure, 10, good),
            1u);
  EXPECT_EQ(count, 1);
}

// §39.4.2: on a success callback the attempt-info pointer is supplied with a
// valid attemptStartTime and no failure expression.
TEST(AssertionCallback, SuccessDeliversAttemptStartTime) {
  AssertionApi api;
  bool had_info = false;
  uint64_t attempt_start = 0;
  bool fail_expr_empty = false;
  api.PlaceAssertionCallback(
      cbAssertionSuccess, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        had_info = (a.info != nullptr);
        if (a.info != nullptr) {
          attempt_start = a.info->attempt_start_time;
          fail_expr_empty = a.info->fail_expr.empty();
        }
      },
      nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 17;
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionSuccess, 17, info), 1u);
  EXPECT_TRUE(had_info);
  EXPECT_EQ(attempt_start, 17u);
  EXPECT_TRUE(fail_expr_empty);
}

// §39.4.2: attemptStartTime is the start time of the actual attempt and serves
// as a unique identifier distinguishing the attempts of a given assertion —
// each delivery carries its own attempt's start time.
TEST(AssertionCallback, AttemptStartTimeDistinguishesAttempts) {
  AssertionApi api;
  uint64_t first_seen = 0;
  uint64_t second_seen = 0;
  int n = 0;
  api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&](const AssertionCallbackArgs& a) {
        if (a.info == nullptr) return;
        if (n == 0) {
          first_seen = a.info->attempt_start_time;
        } else {
          second_seen = a.info->attempt_start_time;
        }
        ++n;
      },
      nullptr);

  AssertionAttemptInfo first;
  first.attempt_start_time = 10;
  AssertionAttemptInfo second;
  second.attempt_start_time = 25;
  api.DeliverAssertionEvent(kA, cbAssertionStart, 10, first);
  api.DeliverAssertionEvent(kA, cbAssertionStart, 25, second);

  EXPECT_EQ(first_seen, 10u);
  EXPECT_EQ(second_seen, 25u);
  EXPECT_NE(first_seen, second_seen);
}

// §39.4.2: a null handle is the value returned on a placement error; removing
// with it removes nothing and reports failure, leaving placed callbacks intact.
TEST(AssertionCallback, RemoveNullHandleReportsNoRemoval) {
  AssertionApi api;
  EXPECT_FALSE(api.RemoveAssertionCallback(0));

  api.PlaceAssertionCallback(cbAssertionStart, kA, vpiAssert, noop_cb, nullptr);
  EXPECT_FALSE(api.RemoveAssertionCallback(0));
  EXPECT_EQ(api.PlacedCallbackCount(), 1u);
}

// -----------------------------------------------------------------------------
// §39.4.2 through its own entry point: vpi_register_assertion_cb() places the
// callback, the placed routine is called with the five arguments the clause
// lists, and vpi_remove_cb() removes it by the handle the placement answered
// with. The rules about which reasons may be placed on which handle are the
// ones above; these cases observe them reaching a PLI application.
// -----------------------------------------------------------------------------

// One call of an application's assertion routine, as the routine was handed it.
struct RecordedAssertionCall {
  PLI_INT32 reason = 0;
  PLI_UINT32 time_high = 0;
  PLI_UINT32 time_low = 0;
  vpiHandle assertion = nullptr;
  bool carried_info = false;
  PLI_UINT32 attempt_high = 0;
  PLI_UINT32 attempt_low = 0;
  PLI_BYTE8* user_data = nullptr;
};

std::vector<RecordedAssertionCall> g_assertion_calls;

PLI_INT32 RecordAssertionCall(PLI_INT32 reason, s_vpi_time* cb_time,
                              vpiHandle assertion, p_vpi_attempt_info info,
                              PLI_BYTE8* user_data) {
  RecordedAssertionCall call;
  call.reason = reason;
  if (cb_time != nullptr) {
    call.time_high = cb_time->high;
    call.time_low = cb_time->low;
  }
  call.assertion = assertion;
  call.carried_info = info != nullptr;
  if (info != nullptr) {
    call.attempt_high = info->attempt_start_time.high;
    call.attempt_low = info->attempt_start_time.low;
  }
  call.user_data = user_data;
  g_assertion_calls.push_back(call);
  return 0;
}

class VpiAssertionCallbackEntry : public ::testing::Test {
 protected:
  void SetUp() override {
    g_assertion_calls.clear();
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

// §39.4.2: "If the callback is successfully placed, a handle to the callback is
// returned." The placement reaches the assertion model - one callback stands
// placed afterwards - and the handle is a callback object.
TEST_F(VpiAssertionCallbackEntry, PlacementAnswersWithAHandleToTheCallback) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);

  vpiHandle cb = vpi_register_assertion_cb(assertion, cbAssertionStart,
                                           &RecordAssertionCall, nullptr);

  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_get(vpiType, cb), vpiCallback);
  EXPECT_EQ(api_.PlacedCallbackCount(), 1u);
}

// §39.4.2: "Once the callback is placed, the user-supplied function shall be
// called each time the specified event occurs on the given assertion", and it
// "shall be supplied the following arguments": the reason, a pointer to the
// time of the callback, the handle for the assertion, a pointer to an attempt
// information structure, and the user data supplied at registration. On a start
// callback the attempt information is the attempt's start time. The times here
// are past the 32-bit boundary, so a routine handed only the low half of either
// would report a different number from the one the event carried.
TEST_F(VpiAssertionCallbackEntry, PlacedRoutineIsCalledWithTheFiveArguments) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  PLI_BYTE8 user_data[] = "from the registration";
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionStart,
                                      &RecordAssertionCall, user_data),
            nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 0x0000000300000004ULL;
  EXPECT_EQ(api_.DeliverAssertionEvent(kA, cbAssertionStart,
                                       0x0000000100000002ULL, info),
            1u);

  ASSERT_EQ(g_assertion_calls.size(), 1u);
  const RecordedAssertionCall& call = g_assertion_calls[0];
  EXPECT_EQ(call.reason, cbAssertionStart);
  EXPECT_EQ(call.time_high, 1u);
  EXPECT_EQ(call.time_low, 2u);
  EXPECT_EQ(call.assertion, assertion);
  ASSERT_TRUE(call.carried_info);
  EXPECT_EQ(call.attempt_high, 3u);
  EXPECT_EQ(call.attempt_low, 4u);
  EXPECT_EQ(call.user_data, user_data);
}

// §39.4.2: "On lock, unlock, disable, enable, reset, kill, pass action, fail
// action, vacuous action, and nonvacuous action callbacks, the returned
// p_vpi_attempt_info info pointer is NULL, and no attempt information is
// available." The routine is still called; what it is handed for the attempt is
// nothing.
TEST_F(VpiAssertionCallbackEntry, ReasonsThatCarryNoAttemptInfoPassNull) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionLock,
                                      &RecordAssertionCall, nullptr),
            nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 7;
  EXPECT_EQ(api_.DeliverAssertionEvent(kA, cbAssertionLock, 9, info), 1u);

  ASSERT_EQ(g_assertion_calls.size(), 1u);
  EXPECT_EQ(g_assertion_calls[0].reason, cbAssertionLock);
  EXPECT_FALSE(g_assertion_calls[0].carried_info);
  EXPECT_EQ(g_assertion_calls[0].user_data, nullptr);
}

// §39.4.2: "These callbacks are specific to a given assertion; placing such a
// callback on one assertion does not cause the callback to trigger on an event
// occurring on a different assertion."
TEST_F(VpiAssertionCallbackEntry, ThePlacementIsSpecificToItsAssertion) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(assertion, cbAssertionStart,
                                      &RecordAssertionCall, nullptr),
            nullptr);

  AssertionAttemptInfo info;
  EXPECT_EQ(api_.DeliverAssertionEvent(kB, cbAssertionStart, 1, info), 0u);
  EXPECT_TRUE(g_assertion_calls.empty());
}

// §39.4.2: "If there were errors on placing the callback, a NULL handle is
// returned." A placement with no assertion to be specific to, one with no
// routine to call, and one whose reason may not be placed on a handle of that
// kind are each such an error, and none of them leaves a callback placed.
TEST_F(VpiAssertionCallbackEntry, ErrorsOnPlacingAnswerWithANullHandle) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  VpiObject module;
  module.type = vpiModule;
  module.name = "top";

  EXPECT_EQ(vpi_register_assertion_cb(nullptr, cbAssertionStart,
                                      &RecordAssertionCall, nullptr),
            nullptr);
  EXPECT_EQ(
      vpi_register_assertion_cb(assertion, cbAssertionStart, nullptr, nullptr),
      nullptr);
  EXPECT_EQ(vpi_register_assertion_cb(&module, cbAssertionStart,
                                      &RecordAssertionCall, nullptr),
            nullptr);

  EXPECT_EQ(api_.PlacedCallbackCount(), 0u);
}

// §39.4.2: "This handle can be used to remove the callback via
// vpi_remove_cb()." Removing it takes the placement out of the model, so the
// event that called the routine before calls nothing after; the handle is spent
// once, and a second removal through it reports no removal.
TEST_F(VpiAssertionCallbackEntry, VpiRemoveCbRemovesThePlacedCallback) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  vpiHandle cb = vpi_register_assertion_cb(assertion, cbAssertionStart,
                                           &RecordAssertionCall, nullptr);
  ASSERT_NE(cb, nullptr);

  AssertionAttemptInfo info;
  ASSERT_EQ(api_.DeliverAssertionEvent(kA, cbAssertionStart, 1, info), 1u);
  ASSERT_EQ(g_assertion_calls.size(), 1u);

  EXPECT_EQ(vpi_remove_cb(cb), 1);
  EXPECT_EQ(api_.PlacedCallbackCount(), 0u);

  EXPECT_EQ(api_.DeliverAssertionEvent(kA, cbAssertionStart, 2, info), 0u);
  EXPECT_EQ(g_assertion_calls.size(), 1u);
  EXPECT_EQ(vpi_remove_cb(cb), 0);
}

// §38.39 is what vpi_remove_cb() otherwise is, and an assertion callback's
// handle is not a row of its table: a simulation callback registered alongside
// is removed by its own handle and by nothing else.
TEST_F(VpiAssertionCallbackEntry,
       ASimulationCallbackIsStillRemovedByItsHandle) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  s_cb_data data = {};
  data.reason = cbEndOfSimulation;
  data.cb_rtn = nullptr;
  vpiHandle sim_cb = vpi_register_cb(&data);
  ASSERT_NE(sim_cb, nullptr);
  vpiHandle assertion_cb = vpi_register_assertion_cb(
      assertion, cbAssertionStart, &RecordAssertionCall, nullptr);
  ASSERT_NE(assertion_cb, nullptr);

  // The assertion callback's handle removes the placement and leaves the
  // simulation callback registered.
  EXPECT_EQ(vpi_remove_cb(assertion_cb), 1);
  EXPECT_EQ(vpi_remove_cb(sim_cb), 1);
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);
}

// §39.1: the assertion API answers out of one model per run. A run that
// installed none still has one - the default - and it is the same one every
// call reaches.
TEST_F(VpiAssertionCallbackEntry, TheDefaultModelStandsWhereNoneWasInstalled) {
  EXPECT_EQ(&GetGlobalAssertionApi(), &api_);

  SetGlobalAssertionApi(nullptr);
  AssertionApi& fallback = GetGlobalAssertionApi();
  EXPECT_NE(&fallback, &api_);
  EXPECT_EQ(&GetGlobalAssertionApi(), &fallback);
}

}  // namespace
