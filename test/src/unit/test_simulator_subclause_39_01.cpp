#include <gtest/gtest.h>

#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_assertion_cb.h"

namespace delta {
namespace {

// §39.1 "General" says what clause 39 describes, and it says it as four items:
// the SystemVerilog assertion API, obtaining assertion handles, assertions
// system callbacks, and the assertion control API functions. The subclause
// carries no rule of its own - each item is written out further down, §39.3.1
// for the handles, §39.4.1 for the system callbacks, §39.4.2 for the
// per-assertion callbacks the API is placed through, and §39.5 for the controls
// - so what §39.1 claims is that this clause provides all four of them. These
// tests take the four one at a time and observe this tool answering for each,
// which is what makes the claim true of it rather than of the document alone.

PLI_INT32 AssertionRoutine(PLI_INT32, s_vpi_time*, vpiHandle,
                           p_vpi_attempt_info, PLI_BYTE8*) {
  return 0;
}

int SimulationCallback(VpiCbData*) { return 0; }

class AssertionApiGeneral : public ::testing::Test {
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

// §39.1, first item - the SystemVerilog assertion API. What the clause puts
// behind that name is reached through vpi_register_assertion_cb(), which is the
// one routine the assertion API adds to the VPI: a C application places its
// callback on an assertion through it and is answered with a handle to the
// callback (§39.4.2).
TEST_F(AssertionApiGeneral, TheAssertionApiIsReachedThroughItsOwnRoutine) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  vpiHandle cb = vpi_register_assertion_cb(assertion, cbAssertionStart,
                                           &AssertionRoutine, nullptr);

  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(api_.PlacedCallbackCount(), 1u);
  EXPECT_EQ(vpi_remove_cb(cb), 1);
}

// §39.1, second item - obtaining assertion handles. §39.3.1 gives two ways of
// getting one, and both answer here: the assertion-class iteration reaches
// every assertion in the design, and the name the assertion was written under
// resolves to the same object.
TEST_F(AssertionApiGeneral, AssertionHandlesAreObtainable) {
  vpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> walked;
  while (vpiHandle h = vpi_scan(it)) walked.push_back(h);
  ASSERT_EQ(walked.size(), 1u);
  EXPECT_EQ(walked[0], assertion);

  EXPECT_EQ(vpi_handle_by_name("handshake_p", nullptr), assertion);
}

// §39.1, third item - assertions system callbacks. These are the §39.4.1
// reasons, which are placed with vpi_register_cb() rather than on an assertion
// of their own: the system as a whole is what they watch. The tool knows them
// as system reasons and accepts the registration.
TEST_F(AssertionApiGeneral, AssertionSystemCallbacksArePlaceable) {
  EXPECT_TRUE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionSysOn));
  EXPECT_TRUE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionSysOff));

  s_cb_data data = {};
  data.reason = cbAssertionSysOff;
  data.cb_rtn = &SimulationCallback;
  EXPECT_NE(vpi_register_cb(&data), nullptr);
}

// §39.1, fourth item - the assertion control API functions. §39.5 splits them
// in two, the system-wide controls of §39.5.1 and the per-assertion controls of
// §39.5.2, and both act: turning the system off stops assertions starting, and
// a control aimed at one assertion reaches that assertion.
TEST_F(AssertionApiGeneral, AssertionControlFunctionsAct) {
  vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  // §39.5.1: the system-wide control reaches the whole assertion system, so
  // turning it off stops assertions starting.
  EXPECT_TRUE(api_.SysControl(vpiAssertionSysOff, {}));
  EXPECT_FALSE(api_.AssertionsStarted());

  // §39.5.2: the per-assertion control reaches the one assertion it names, and
  // what it did there is readable afterwards.
  EXPECT_TRUE(api_.Control(vpiAssertionDisableFailAction, "handshake_p"));
  EXPECT_FALSE(api_.AssertionFailActionEnabled("handshake_p"));
}

}  // namespace
}  // namespace delta
