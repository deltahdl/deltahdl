// §20.11, Table 20-8: the VPI callbacks an assertion control task's call
// raises. A call naming no scope or assertion raises the assertion system
// callback of §39.4.1 its control_type selects; a call naming some raises the
// assertion callbacks of §39.4.2 on each assertion it selects.
#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

std::vector<int> g_system_reasons;
std::vector<std::pair<int, std::string>> g_assertion_reasons;

PLI_INT32 RecordSystemReason(s_cb_data* data) {
  g_system_reasons.push_back(data->reason);
  return 0;
}

PLI_INT32 RecordAssertionReason(PLI_INT32 reason, s_vpi_time* /*cb_time*/,
                                vpiHandle assertion,
                                p_vpi_attempt_info /*info*/,
                                PLI_BYTE8* /*user_data*/) {
  g_assertion_reasons.emplace_back(reason, vpi_get_str(vpiName, assertion));
  return 0;
}

// Places a callback for each of `reasons` on the assertion `name` of `top`.
void PlaceOn(const char* name, std::initializer_list<int> reasons) {
  vpiHandle it =
      vpi_iterate(vpiAssertion, vpi_handle_by_name(VpiText("top"), nullptr));
  while (vpiHandle assertion = it == nullptr ? nullptr : vpi_scan(it)) {
    const char* own = vpi_get_str(vpiName, assertion);
    if (own == nullptr || std::string(own) != name) continue;
    for (int reason : reasons) {
      vpi_register_assertion_cb(assertion, reason, &RecordAssertionReason,
                                nullptr);
    }
  }
}

// The calltf of $place, which places the callbacks the run is to raise once
// the run has built the assertions they are placed on.
PLI_INT32 PlaceCallbacks(PLI_BYTE8* /*user_data*/) {
  PlaceOn("a1", {cbAssertionDisable, cbAssertionReset});
  PlaceOn("a2", {cbAssertionDisable, cbAssertionReset});
  return 0;
}

class AssertControlCallbacks : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    SetGlobalAssertionApi(&api_);
    g_system_reasons.clear();
    g_assertion_reasons.clear();
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    VpiDesignRun::TearDown();
  }

  AssertionApi api_;
};

// Table 20-8: $assertoff and $assertcontrol(5) applied to the whole design
// raise cbAssertionSysOff and cbAssertionSysKill, and a control_type Table
// 20-5 does not list raises nothing.
TEST_F(AssertControlCallbacks, AControlOfTheWholeDesignRaisesItsSystemReason) {
  for (int reason : {cbAssertionSysOff, cbAssertionSysKill, cbAssertionSysOn}) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordSystemReason;
    ASSERT_NE(vpi_register_cb(&cb), nullptr);
  }
  Run("module top;\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    $assertcontrol(5);\n"
      "    $assertcontrol(12);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(g_system_reasons,
            (std::vector<int>{cbAssertionSysOff, cbAssertionSysKill}));
}

// Table 20-8: $assertoff naming a1 raises cbAssertionDisable on a1 alone, and
// $assertkill naming a2 raises cbAssertionReset and then cbAssertionDisable on
// a2 alone; no system callback is raised by either.
TEST_F(AssertControlCallbacks, AControlNamingAssertionsRaisesTheirReasons) {
  s_vpi_systf_data place = {};
  place.type = vpiSysTask;
  place.tfname = VpiText("$place");
  place.calltf = &PlaceCallbacks;
  ASSERT_NE(vpi_register_systf(&place), nullptr);
  s_cb_data sys = {};
  sys.reason = cbAssertionSysOff;
  sys.cb_rtn = &RecordSystemReason;
  ASSERT_NE(vpi_register_cb(&sys), nullptr);
  Run("module top;\n"
      "  logic clk = 0;\n"
      "  a1: assert property (@(posedge clk) 1);\n"
      "  a2: assert property (@(posedge clk) 1);\n"
      "  initial begin\n"
      "    $place;\n"
      "    $assertoff(0, a1);\n"
      "    $assertkill(0, a2);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(g_assertion_reasons, (std::vector<std::pair<int, std::string>>{
                                     {cbAssertionDisable, "a1"},
                                     {cbAssertionReset, "a2"},
                                     {cbAssertionDisable, "a2"}}));
  EXPECT_TRUE(g_system_reasons.empty());
}

}  // namespace
