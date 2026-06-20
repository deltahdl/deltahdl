#include <gtest/gtest.h>

#include <iterator>
#include <string>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";
constexpr const char* kB = "top.a2";

auto NoopCb = [](const AssertionCallbackArgs&) {};

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
      cbAssertionStart, kA, vpiAssert, NoopCb, nullptr);
  EXPECT_NE(h, 0u);
  EXPECT_EQ(api.PlacedCallbackCount(), 1u);

  EXPECT_TRUE(api.RemoveAssertionCallback(h));
  EXPECT_EQ(api.PlacedCallbackCount(), 0u);
  // Removing an already-removed handle reports no removal.
  EXPECT_FALSE(api.RemoveAssertionCallback(h));

  // An empty handle is an error: the NULL handle is returned.
  EXPECT_EQ(api.PlaceAssertionCallback(cbAssertionStart, "", vpiAssert, NoopCb,
                                       nullptr),
            0u);
}

// §39.4.2: an unrecognized reason cannot be placed; the NULL handle is
// returned.
TEST(AssertionCallback, UnknownReasonErrorsWithNullHandle) {
  AssertionApi api;
  EXPECT_EQ(api.PlaceAssertionCallback(vpiAssertionSysOff, kA, vpiAssert,
                                       NoopCb, nullptr),
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
                                       NoopCb, nullptr),
            0u);
  // The same reason is accepted on a concurrent assertion statement.
  EXPECT_NE(api.PlaceAssertionCallback(cbAssertionDisable, kA, vpiAssert,
                                       NoopCb, nullptr),
            0u);
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

  api.PlaceAssertionCallback(cbAssertionStart, kA, vpiAssert, NoopCb, nullptr);
  EXPECT_FALSE(api.RemoveAssertionCallback(0));
  EXPECT_EQ(api.PlacedCallbackCount(), 1u);
}

}  // namespace
