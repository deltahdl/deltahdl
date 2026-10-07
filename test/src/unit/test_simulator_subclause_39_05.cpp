#include <gtest/gtest.h>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §39.5 "Control functions" says what the subclause is for in one sentence: it
// shows how to control the assertion system and single assertions. Two controls
// and one routine: §39.5.1 controls the assertion system through vpi_control()
// with a scope handle, and §39.5.2 controls one assertion through vpi_control()
// with that assertion's handle, with an attempt start time where the control
// names an attempt and a step control constant on top of it for the stepping
// one. These tests ask for each through vpi_control() and read back what the
// control did.

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

// §39.5.1: the assertion system is controlled by vpi_control() with one of the
// listed constants and, as its second argument, the vpiHandle of a scope; a
// NULL handle makes the control reach every assertion, whatever its scope.
// Turning the system off through the routine stops assertions starting, and the
// handle is what says how far the control reaches.
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

// §39.5.2: the second argument must be a handle to an assertion, and the
// control reaches that assertion. Disabling one leaves the other enabled: the
// handle is what the control is aimed by.
TEST_F(AssertionControlFunctions, AnAssertionIsControlledThroughVpiControl) {
  VpiHandle first = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  vpi_ctx_.CreateAssertion("overflow_p", vpiAssert);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, first), 1);
  EXPECT_FALSE(api_.AssertionEnabled("handshake_p"));
  EXPECT_TRUE(api_.AssertionEnabled("overflow_p"));

  EXPECT_EQ(vpi_control(vpiAssertionDisableFailAction, first), 1);
  EXPECT_FALSE(api_.AssertionFailActionEnabled("handshake_p"));
}

// §39.5.2: the handle must be one of an assertion statement; a sequence or
// property instance's handle will not do. A handle that is neither an assertion
// statement nor a handle at all controls nothing, and the routine reports that
// it did not.
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

// §39.5.2: for the controls that name an attempt, the third argument is the
// attempt's start time, passed as a pointer to a properly filled-in s_vpi_time
// structure. vpiAssertionKill discards the attempt that started at that time,
// and the attempt is named by the time rather than by the assertion alone.
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

  // The attempt that started at 10 is gone; the one that started at 20 stands.
  EXPECT_EQ(api_.AssertionAttemptsInProgress("handshake_p"), 1u);
}

// §39.5.2: the fourth argument is a step control constant -
// vpiAssertionEnableStep enables step callbacks for the attempt named, which is
// the attempt the third argument names, and vpiAssertionClockSteps is the
// constant that says on what basis they occur.
TEST_F(AssertionControlFunctions, SteppingIsEnabledForTheNamedAttempt) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  // §39.5.2: an attempt's stepping mode is fixed once that attempt has started,
  // so the attempt this names is one that has not started yet.
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

}  // namespace
}  // namespace delta
