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

PLI_INT32 RecordAssertionReason(PLI_INT32 reason, s_vpi_time*,
                                vpiHandle assertion, p_vpi_attempt_info,
                                PLI_BYTE8*) {
  g_assertion_reasons.emplace_back(reason, vpi_get_str(vpiName, assertion));
  return 0;
}

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

PLI_INT32 PlaceCallbacks(PLI_BYTE8*) {
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
            (std::vector<int>{cbAssertionSysOn, cbAssertionSysOff,
                              cbAssertionSysKill}));
}

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
