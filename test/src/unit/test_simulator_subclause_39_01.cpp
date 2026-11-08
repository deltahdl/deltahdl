#include <gtest/gtest.h>

#include <vector>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 AssertionRoutine(PLI_INT32, s_vpi_time*, vpiHandle,
                           p_vpi_attempt_info, PLI_BYTE8*) {
  return 0;
}

int SimulationCallback(s_cb_data*) { return 0; }

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

TEST_F(AssertionApiGeneral, TheAssertionApiIsReachedThroughItsOwnRoutine) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  vpiHandle cb = vpi_register_assertion_cb(
      VpiHandleOf(assertion), cbAssertionStart, &AssertionRoutine, nullptr);

  ASSERT_NE(cb, nullptr);
  EXPECT_EQ(api_.PlacedCallbackCount(), 1u);
  EXPECT_EQ(vpi_remove_cb(cb), 1);
}

TEST_F(AssertionApiGeneral, AssertionHandlesAreObtainable) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> walked;
  while (vpiHandle h = vpi_scan(it)) walked.push_back(h);
  ASSERT_EQ(walked.size(), 1u);
  EXPECT_EQ(VpiObjectOf(walked[0]), assertion);

  EXPECT_EQ(VpiObjectOf(vpi_handle_by_name(VpiText("handshake_p"), nullptr)),
            assertion);
}

TEST_F(AssertionApiGeneral, AssertionSystemCallbacksArePlaceable) {
  EXPECT_TRUE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionSysOn));
  EXPECT_TRUE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionSysOff));

  s_cb_data data = {};
  data.reason = cbAssertionSysOff;
  data.cb_rtn = &SimulationCallback;
  EXPECT_NE(vpi_register_cb(&data), nullptr);
}

TEST_F(AssertionApiGeneral, AssertionControlFunctionsAct) {
  vpi_ctx_.CreateAssertion("handshake_p", vpiAssert);

  EXPECT_TRUE(api_.SysControl(vpiAssertionSysOff, {}));
  EXPECT_FALSE(api_.AssertionsStarted());

  EXPECT_TRUE(api_.Control(vpiAssertionDisableFailAction, "handshake_p"));
  EXPECT_FALSE(api_.AssertionFailActionEnabled("handshake_p"));
}

}  // namespace
}  // namespace delta
