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

class AssertionControlFunctions : public ::testing::Test {
 protected:
  void SetUp() override {
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

TEST_F(AssertionControlFunctions, TheSystemIsControlledThroughVpiControl) {
  VpiHandle scope = vpi_ctx_.CreateModule("dut", "dut");

  EXPECT_EQ(vpi_control(vpiAssertionSysOff, static_cast<vpiHandle>(nullptr)),
            1);
  EXPECT_FALSE(api_.AssertionsStarted());
  EXPECT_TRUE(api_.LastControlGlobal());

  EXPECT_EQ(vpi_control(vpiAssertionSysOn, scope), 1);
  EXPECT_TRUE(api_.AssertionsStarted());
  EXPECT_FALSE(api_.LastControlGlobal());
}

TEST_F(AssertionControlFunctions, AnAssertionIsControlledThroughVpiControl) {
  VpiHandle first = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  vpi_ctx_.CreateAssertion("overflow_p", vpiAssert);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, first), 1);
  EXPECT_FALSE(api_.AssertionEnabled("handshake_p"));
  EXPECT_TRUE(api_.AssertionEnabled("overflow_p"));

  EXPECT_EQ(vpi_control(vpiAssertionDisableFailAction, first), 1);
  EXPECT_FALSE(api_.AssertionFailActionEnabled("handshake_p"));
}

TEST_F(AssertionControlFunctions, OnlyAnAssertionStatementHandleIsValid) {
  VpiHandle sequence = vpi_ctx_.CreateAssertion("handshake_s", vpiSequenceInst);
  VpiHandle property = vpi_ctx_.CreateAssertion("handshake_q", vpiPropertyInst);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, sequence), 0);
  EXPECT_EQ(vpi_control(vpiAssertionDisable, property), 0);
  EXPECT_EQ(vpi_control(vpiAssertionDisable, static_cast<vpiHandle>(nullptr)),
            0);

  EXPECT_TRUE(api_.AssertionEnabled("handshake_s"));
  EXPECT_TRUE(api_.AssertionEnabled("handshake_q"));
}

TEST_F(AssertionControlFunctions, AnAttemptIsNamedByItsStartTime) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  api_.NoteAssertionAttemptStarted("handshake_p", 10);
  api_.NoteAssertionAttemptStarted("handshake_p", 20);
  ASSERT_EQ(api_.AssertionAttemptsInProgress("handshake_p"), 2u);

  s_vpi_time attempt = {};
  attempt.type = vpiSimTime;
  attempt.high = 0;
  attempt.low = 10;
  EXPECT_EQ(vpi_control(vpiAssertionKill, assertion, &attempt), 1);

  EXPECT_EQ(api_.AssertionAttemptsInProgress("handshake_p"), 1u);
}

TEST_F(AssertionControlFunctions, SteppingIsEnabledForTheNamedAttempt) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  s_vpi_time attempt = {};
  attempt.type = vpiSimTime;
  attempt.low = 10;
  EXPECT_EQ(vpi_control(vpiAssertionEnableStep, assertion, &attempt,
                        vpiAssertionClockSteps),
            1);
  api_.NoteAssertionAttemptStarted("handshake_p", 10);
  EXPECT_TRUE(api_.AssertionStepEnabled("handshake_p", 10));

  EXPECT_EQ(vpi_control(vpiAssertionDisableStep, assertion, &attempt), 1);
  EXPECT_FALSE(api_.AssertionStepEnabled("handshake_p", 10));
}

std::vector<int>& CalledReasons() {
  static std::vector<int> reasons;
  return reasons;
}
std::vector<bool>& CalledWithInfo() {
  static std::vector<bool> with_info;
  return with_info;
}

PLI_INT32 RecordSystemCallback(p_cb_data data) {
  CalledReasons().push_back(data->reason);
  return 0;
}

PLI_INT32 RecordAssertionCallback(PLI_INT32 reason, p_vpi_time, vpiHandle,
                                  p_vpi_attempt_info info, PLI_BYTE8*) {
  CalledReasons().push_back(reason);
  CalledWithInfo().push_back(info != nullptr);
  return 0;
}

TEST_F(AssertionControlFunctions, ASystemControlCallsItsSystemCallback) {
  CalledReasons().clear();
  for (int reason : {cbAssertionSysOff, cbAssertionSysOn, cbAssertionSysReset,
                     cbAssertionSysLock}) {
    s_cb_data data = {};
    data.reason = reason;
    data.cb_rtn = &RecordSystemCallback;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
  }

  auto* none = static_cast<vpiHandle>(nullptr);
  EXPECT_EQ(vpi_control(vpiAssertionSysOff, none), 1);
  EXPECT_EQ(vpi_control(vpiAssertionSysOn, none), 1);
  EXPECT_EQ(vpi_control(vpiAssertionSysReset, none), 1);
  EXPECT_EQ(vpi_control(vpiAssertionSysLock, none), 1);
  EXPECT_EQ(vpi_control(vpiAssertionSysOff, none), 0);

  EXPECT_EQ(CalledReasons(),
            (std::vector<int>{cbAssertionSysOff, cbAssertionSysOn,
                              cbAssertionSysReset, cbAssertionSysLock}));
}

TEST_F(AssertionControlFunctions, AnAssertionControlCallsItsAssertionCallback) {
  CalledReasons().clear();
  CalledWithInfo().clear();
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  for (int reason : {cbAssertionDisable, cbAssertionEnable,
                     cbAssertionDisableFailAction, cbAssertionKill}) {
    ASSERT_NE(vpi_register_assertion_cb(VpiHandleOf(assertion), reason,
                                        &RecordAssertionCallback, nullptr),
              nullptr);
  }

  EXPECT_EQ(vpi_control(vpiAssertionDisable, assertion), 1);
  EXPECT_EQ(vpi_control(vpiAssertionEnable, assertion), 1);
  EXPECT_EQ(vpi_control(vpiAssertionDisableFailAction, assertion), 1);
  s_vpi_time attempt = {};
  attempt.type = vpiSimTime;
  attempt.low = 10;
  EXPECT_EQ(vpi_control(vpiAssertionKill, assertion, &attempt), 1);
  EXPECT_EQ(vpi_control(vpiAssertionLock, assertion), 1);
  EXPECT_EQ(vpi_control(vpiAssertionDisable, assertion), 0);

  EXPECT_EQ(CalledReasons(),
            (std::vector<int>{cbAssertionDisable, cbAssertionEnable,
                              cbAssertionDisableFailAction, cbAssertionKill}));
  EXPECT_EQ(CalledWithInfo(), (std::vector<bool>{false, false, false, false}));
}

}  // namespace
}  // namespace delta
