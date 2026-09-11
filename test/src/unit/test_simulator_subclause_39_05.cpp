#include <gtest/gtest.h>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §39.5 "Control functions" says what the subclause is for in one sentence:
// "This subclause defines how to obtain assertion system control and assertion
// control information." Two controls and one routine: §39.5.1 controls the
// assertion system through vpi_control() with a scope handle, and §39.5.2
// controls one assertion through vpi_control() with that assertion's handle,
// with an attempt start time where the control names an attempt and a step
// control constant on top of it for the stepping one. These tests ask for each
// through vpi_control() and read back what the control did.

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

// §39.5.1: "To control the assertion system, use vpi_control() with one of the
// following constants and a second handle argument that is a vpiHandle for a
// scope. A NULL handle signifies that the control applies to all assertions
// regardless of scope." Turning the system off through the routine stops
// assertions starting, and the handle is what says how far the control reaches.
TEST_F(AssertionControlFunctions, TheSystemIsControlledThroughVpiControl) {
  vpiHandle scope = vpi_ctx_.CreateModule("dut", "dut");

  EXPECT_EQ(vpi_control(vpiAssertionSysOff, static_cast<vpiHandle>(nullptr)),
            1);
  EXPECT_FALSE(api_.AssertionsStarted());
  EXPECT_TRUE(api_.LastControlGlobal());

  EXPECT_EQ(vpi_control(vpiAssertionSysOn, scope), 1);
  EXPECT_TRUE(api_.AssertionsStarted());
  EXPECT_FALSE(api_.LastControlGlobal());
}

// §39.5.2: the second argument "shall be a valid assertion handle", and the
// control reaches that assertion. Disabling one leaves the other enabled: the
// handle is what the control is aimed by.
TEST_F(AssertionControlFunctions, AnAssertionIsControlledThroughVpiControl) {
  vpiHandle first = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  vpi_ctx_.CreateAssertion("overflow_p", vpiAssert);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, first), 1);
  EXPECT_FALSE(api_.AssertionEnabled("handshake_p"));
  EXPECT_TRUE(api_.AssertionEnabled("overflow_p"));

  EXPECT_EQ(vpi_control(vpiAssertionDisableFailAction, first), 1);
  EXPECT_FALSE(api_.AssertionFailActionEnabled("handshake_p"));
}

// §39.5.2: "Only assertion statement handles are valid here, not sequence or
// property instances." A handle that is neither an assertion statement nor a
// handle at all controls nothing, and the routine reports that it did not.
TEST_F(AssertionControlFunctions, OnlyAnAssertionStatementHandleIsValid) {
  vpiHandle sequence = vpi_ctx_.CreateAssertion("handshake_s", vpiSequenceInst);
  vpiHandle property = vpi_ctx_.CreateAssertion("handshake_q", vpiPropertyInst);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, sequence), 0);
  EXPECT_EQ(vpi_control(vpiAssertionDisable, property), 0);
  EXPECT_EQ(vpi_control(vpiAssertionDisable, static_cast<vpiHandle>(nullptr)),
            0);

  EXPECT_TRUE(api_.AssertionEnabled("handshake_s"));
  EXPECT_TRUE(api_.AssertionEnabled("handshake_q"));
}

// §39.5.2: for the controls that name an attempt, "the third argument shall be
// an attempt start time (as a pointer to a correctly initialized s_vpi_time
// structure)". vpiAssertionKill discards the attempt that started at that time,
// and the attempt is named by the time rather than by the assertion alone.
TEST_F(AssertionControlFunctions, AnAttemptIsNamedByItsStartTime) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
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

// §39.5.2: "the fourth argument shall be a step control constant" -
// vpiAssertionEnableStep enables step callbacks "for this assertion attempt",
// which is the attempt the third argument names, and vpiAssertionClockSteps is
// the constant that says on what basis they occur.
TEST_F(AssertionControlFunctions, SteppingIsEnabledForTheNamedAttempt) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);
  api_.NoteAssertionAttemptStarted("handshake_p", 10);

  s_vpi_time attempt = {};
  attempt.type = vpiSimTime;
  attempt.low = 10;
  EXPECT_EQ(vpi_control(vpiAssertionEnableStep, assertion, &attempt,
                        vpiAssertionClockSteps),
            1);
  EXPECT_TRUE(api_.AssertionStepEnabled("handshake_p", 10));

  EXPECT_EQ(vpi_control(vpiAssertionDisableStep, assertion, &attempt), 1);
  EXPECT_FALSE(api_.AssertionStepEnabled("handshake_p", 10));
}

}  // namespace
}  // namespace delta
