#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <iterator>
#include <string>
#include <vector>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";
constexpr const char* kB = "top.a2";

auto noop_cb = [](const AssertionCallbackArgs&) {};

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
  EXPECT_FALSE(AssertionApi::IsAssertionCallbackReason(vpiAssertionSysOff));
}

TEST(AssertionCallback, ApiSurfaceMatchesPrototype) {
  s_vpi_assertion_step_info step{};
  step.matched_expression_count = 0;
  step.matched_exprs = nullptr;
  step.stateFrom = 0;
  step.stateTo = 1;

  s_vpi_attempt_info info{};
  info.detail.step = &step;
  (void)info.attemptStartTime;

  vpi_assertion_callback_func* fn = nullptr;
  (void)fn;

  vpiHandle h =
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

TEST(AssertionCallback, PlaceReturnsHandleAndRemovesByHandle) {
  AssertionApi api;
  AssertionCallbackHandle h = api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert, noop_cb, nullptr);
  EXPECT_NE(h, 0u);
  EXPECT_EQ(api.PlacedCallbackCount(), 1u);

  EXPECT_TRUE(api.RemoveAssertionCallback(h));
  EXPECT_EQ(api.PlacedCallbackCount(), 0u);
  EXPECT_FALSE(api.RemoveAssertionCallback(h));

  EXPECT_EQ(api.PlaceAssertionCallback(cbAssertionStart, "", vpiAssert, noop_cb,
                                       nullptr),
            0u);
}

TEST(AssertionCallback, UnknownReasonErrorsWithNullHandle) {
  AssertionApi api;
  EXPECT_EQ(api.PlaceAssertionCallback(vpiAssertionSysOff, kA, vpiAssert,
                                       noop_cb, nullptr),
            0u);
  EXPECT_EQ(api.PlacedCallbackCount(), 0u);
}

TEST(AssertionCallback, HandleTypeValidity) {
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionDisable, vpiAssert));
  EXPECT_TRUE(AssertionApi::IsReasonValidForHandle(cbAssertionStepSuccess,
                                                   vpiImmediateAssert));
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionStart, vpiRestrict));
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionDisable, vpiRestrict));
  EXPECT_TRUE(
      AssertionApi::IsReasonValidForHandle(cbAssertionStart, vpiSequenceInst));
  EXPECT_TRUE(AssertionApi::IsReasonValidForHandle(cbAssertionSuccess,
                                                   vpiPropertyInst));
  EXPECT_TRUE(AssertionApi::IsReasonValidForHandle(cbAssertionFailure,
                                                   vpiPropertyInst));

  EXPECT_FALSE(AssertionApi::IsReasonValidForHandle(cbAssertionDisable,
                                                    vpiSequenceInst));
  EXPECT_FALSE(AssertionApi::IsReasonValidForHandle(cbAssertionStepSuccess,
                                                    vpiPropertyInst));
  EXPECT_FALSE(
      AssertionApi::IsReasonValidForHandle(cbAssertionStart, vpiSequenceDecl));
  EXPECT_FALSE(
      AssertionApi::IsReasonValidForHandle(cbAssertionSuccess, vpiProperty));
  EXPECT_FALSE(AssertionApi::IsReasonValidForHandle(cbAssertionFailure,
                                                    vpiPropertyDecl));
  EXPECT_FALSE(
      AssertionApi::IsReasonValidForHandle(cbAssertionStart, vpiModule));
}

TEST(AssertionCallback, PlaceRejectsReasonInvalidForHandle) {
  AssertionApi api;
  EXPECT_EQ(api.PlaceAssertionCallback(cbAssertionDisable, kA, vpiSequenceInst,
                                       noop_cb, nullptr),
            0u);
  EXPECT_NE(api.PlaceAssertionCallback(cbAssertionDisable, kA, vpiAssert,
                                       noop_cb, nullptr),
            0u);
}

TEST(AssertionCallback, PlacesOnEveryAssertionStatementHandleType) {
  int handle_types[] = {vpiAssert,          vpiAssume,
                        vpiCover,           vpiImmediateAssert,
                        vpiImmediateAssume, vpiImmediateCover};
  for (int handle_type : handle_types) {
    AssertionApi api;
    EXPECT_NE(api.PlaceAssertionCallback(cbAssertionKill, kA, handle_type,
                                         noop_cb, nullptr),
              0u);
    EXPECT_EQ(api.PlacedCallbackCount(), 1u);
  }
}

TEST(AssertionCallback, FiresPerAssertionUntilRemoved) {
  AssertionApi api;
  int count = 0;
  AssertionCallbackHandle h = api.PlaceAssertionCallback(
      cbAssertionStart, kA, vpiAssert,
      [&count](const AssertionCallbackArgs&) { ++count; }, nullptr);

  AssertionAttemptInfo info;
  info.attempt_start_time = 10;

  api.DeliverAssertionEvent(kB, cbAssertionStart, 10, info);
  EXPECT_EQ(count, 0);

  api.DeliverAssertionEvent(kA, cbAssertionStart, 10, info);
  api.DeliverAssertionEvent(kA, cbAssertionStart, 12, info);
  EXPECT_EQ(count, 2);

  api.RemoveAssertionCallback(h);
  api.DeliverAssertionEvent(kA, cbAssertionStart, 14, info);
  EXPECT_EQ(count, 2);
}

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

TEST(AssertionCallback, FailureCallbackFiresWhenPlacedOnPropertyInstance) {
  AssertionApi api;
  int count = 0;
  std::string fail_expr;
  uint64_t attempt_start = 0;
  AssertionCallbackHandle h = api.PlaceAssertionCallback(
      cbAssertionFailure, kA, vpiPropertyInst,
      [&](const AssertionCallbackArgs& a) {
        ++count;
        if (a.info != nullptr) {
          fail_expr = a.info->fail_expr;
          attempt_start = a.info->attempt_start_time;
        }
      },
      nullptr);
  EXPECT_NE(h, 0u);

  AssertionAttemptInfo info;
  info.attempt_start_time = 8;
  info.fail_expr = "req && !gnt";
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionFailure, 8, info), 1u);

  EXPECT_EQ(count, 1);
  EXPECT_EQ(fail_expr, "req && !gnt");
  EXPECT_EQ(attempt_start, 8u);
}

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

  AssertionAttemptInfo success;
  success.step.state_from = 0;
  success.step.state_to = 2;
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepSuccess, 10, success),
            1u);
  EXPECT_EQ(count, 1);
  EXPECT_EQ(last_from, 0);
  EXPECT_EQ(last_to, 2);
  EXPECT_EQ(last_exprs, 0u);

  AssertionAttemptInfo failure;
  failure.step.state_from = 2;
  failure.step.state_to = 1;
  failure.step.matched_exprs = {"x"};
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepFailure, 11, failure),
            1u);
  EXPECT_EQ(count, 2);
  EXPECT_EQ(last_exprs, 1u);
}

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

  AssertionAttemptInfo bad;
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepFailure, 10, bad), 0u);
  EXPECT_EQ(count, 0);

  AssertionAttemptInfo good;
  good.step.matched_exprs = {"e"};
  EXPECT_EQ(api.DeliverAssertionEvent(kA, cbAssertionStepFailure, 10, good),
            1u);
  EXPECT_EQ(count, 1);
}

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

TEST(AssertionCallback, RemoveNullHandleReportsNoRemoval) {
  AssertionApi api;
  EXPECT_FALSE(api.RemoveAssertionCallback(0));

  api.PlaceAssertionCallback(cbAssertionStart, kA, vpiAssert, noop_cb, nullptr);
  EXPECT_FALSE(api.RemoveAssertionCallback(0));
  EXPECT_EQ(api.PlacedCallbackCount(), 1u);
}

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
    call.attempt_high = info->attemptStartTime.high;
    call.attempt_low = info->attemptStartTime.low;
  }
  call.user_data = static_cast<PLI_BYTE8*>(user_data);
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

TEST_F(VpiAssertionCallbackEntry, PlacementAnswersWithAHandleToTheCallback) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);

  vpiHandle cb = vpi_register_assertion_cb(
      VpiHandleOf(assertion), cbAssertionStart, &RecordAssertionCall, nullptr);

  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(vpi_get(vpiType, cb), vpiCallback);
  EXPECT_EQ(api_.PlacedCallbackCount(), 1u);
}

TEST_F(VpiAssertionCallbackEntry, PlacedRoutineIsCalledWithTheFiveArguments) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  PLI_BYTE8 user_data[] = "from the registration";
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionStart,
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
  EXPECT_EQ(VpiObjectOf(call.assertion), assertion);
  ASSERT_TRUE(call.carried_info);
  EXPECT_EQ(call.attempt_high, 3u);
  EXPECT_EQ(call.attempt_low, 4u);
  EXPECT_EQ(call.user_data, user_data);
}

TEST_F(VpiAssertionCallbackEntry, ReasonsThatCarryNoAttemptInfoPassNull) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionLock,
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

TEST_F(VpiAssertionCallbackEntry, ThePlacementIsSpecificToItsAssertion) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionStart,
                                      &RecordAssertionCall, nullptr),
            nullptr);

  AssertionAttemptInfo info;
  EXPECT_EQ(api_.DeliverAssertionEvent(kB, cbAssertionStart, 1, info), 0u);
  EXPECT_TRUE(g_assertion_calls.empty());
}

TEST_F(VpiAssertionCallbackEntry, ErrorsOnPlacingAnswerWithANullHandle) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  VpiObject module;
  module.type = vpiModule;
  module.name = "top";

  EXPECT_EQ(vpi_register_assertion_cb(nullptr, cbAssertionStart,
                                      &RecordAssertionCall, nullptr),
            nullptr);
  EXPECT_EQ(vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionStart,
                                      nullptr, nullptr),
            nullptr);
  EXPECT_EQ(vpi_register_assertion_cb(VpiHandleOf(&module), cbAssertionStart,
                                      &RecordAssertionCall, nullptr),
            nullptr);

  EXPECT_EQ(api_.PlacedCallbackCount(), 0u);
}

TEST_F(VpiAssertionCallbackEntry, VpiRemoveCbRemovesThePlacedCallback) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  vpiHandle cb = vpi_register_assertion_cb(
      VpiHandleOf(assertion), cbAssertionStart, &RecordAssertionCall, nullptr);
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

TEST_F(VpiAssertionCallbackEntry,
       ASimulationCallbackIsStillRemovedByItsHandle) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  s_cb_data data = {};
  data.reason = cbEndOfSimulation;
  data.cb_rtn = nullptr;
  vpiHandle sim_cb = vpi_register_cb(&data);
  ASSERT_NE(sim_cb, nullptr);
  vpiHandle assertion_cb = vpi_register_assertion_cb(
      VpiHandleOf(assertion), cbAssertionStart, &RecordAssertionCall, nullptr);
  ASSERT_NE(assertion_cb, nullptr);

  EXPECT_EQ(vpi_remove_cb(assertion_cb), 1);
  EXPECT_EQ(vpi_remove_cb(sim_cb), 1);
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);
}

TEST_F(VpiAssertionCallbackEntry, TheDefaultModelStandsWhereNoneWasInstalled) {
  EXPECT_EQ(&GetGlobalAssertionApi(), &api_);

  SetGlobalAssertionApi(nullptr);
  AssertionApi& fallback = GetGlobalAssertionApi();
  EXPECT_NE(&fallback, &api_);
  EXPECT_EQ(&GetGlobalAssertionApi(), &fallback);
}

TEST_F(VpiAssertionCallbackEntry, APlacementRecordsWhatAControlSelectsBy) {
  VpiHandle observed = vpi_ctx_.CreateAssertion(kA, vpiImmediateAssert);
  observed->is_deferred = true;
  VpiHandle final_cover = vpi_ctx_.CreateAssertion(kB, vpiImmediateCover);
  final_cover->is_deferred = true;
  final_cover->is_final = true;
  for (VpiHandle assertion : {observed, final_cover}) {
    ASSERT_NE(
        vpi_register_assertion_cb(VpiHandleOf(assertion), cbAssertionDisable,
                                  &RecordAssertionCall, nullptr),
        nullptr);
  }

  const auto& targets = api_.ControlTargets();
  ASSERT_EQ(targets.size(), 2u);
  EXPECT_EQ(targets.at(kA).type_bit, 4u);
  EXPECT_EQ(targets.at(kA).directive_bit, 1u);
  EXPECT_EQ(targets.at(kB).type_bit, 8u);
  EXPECT_EQ(targets.at(kB).directive_bit, 2u);
}

}  // namespace
