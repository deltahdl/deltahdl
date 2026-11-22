#include <gtest/gtest.h>

#include <deque>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<int>& CountsRead() {
  static std::vector<int> counts;
  return counts;
}

std::deque<int>& CallCounts() {
  static std::deque<int> counts;
  return counts;
}

vpiHandle& LastCall() {
  static vpiHandle call = nullptr;
  return call;
}

int compiletf_marker = 0;
void* read_in_calltf = nullptr;

PLI_INT32 CountCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  LastCall() = call;
  auto* count = static_cast<int*>(vpi_get_userdata(call));
  if (count == nullptr) count = &CallCounts().emplace_back(0);
  ++*count;
  CountsRead().push_back(*count);
  vpi_put_userdata(call, count);
  return 0;
}

PLI_INT32 MarkCompiletf(PLI_BYTE8*) {
  vpi_put_userdata(vpi_handle(vpiSysTfCall, nullptr), &compiletf_marker);
  return 0;
}

PLI_INT32 ReadMarkCalltf(PLI_BYTE8*) {
  read_in_calltf = vpi_get_userdata(vpi_handle(vpiSysTfCall, nullptr));
  return 0;
}

class UserDataOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    CountsRead().clear();
    CallCounts().clear();
    LastCall() = nullptr;
    read_in_calltf = nullptr;
    s_vpi_systf_data task = {};
    task.type = vpiSysTask;
    task.tfname = VpiText("$count");
    task.calltf = &CountCalltf;
    count_systf_ = vpi_register_systf(&task);
    ASSERT_NE(count_systf_, nullptr);
    s_vpi_systf_data func = {};
    func.type = vpiSysFunc;
    func.sysfunctype = vpiIntFunc;
    func.tfname = VpiText("$fcount");
    func.calltf = &CountCalltf;
    ASSERT_NE(vpi_register_systf(&func), nullptr);
    s_vpi_systf_data mark = {};
    mark.type = vpiSysTask;
    mark.tfname = VpiText("$mark");
    mark.compiletf = &MarkCompiletf;
    mark.calltf = &ReadMarkCalltf;
    ASSERT_NE(vpi_register_systf(&mark), nullptr);
  }

  void ExpectCounts(const std::vector<int>& counts) {
    EXPECT_EQ(CountsRead(), counts);
  }

  vpiHandle count_systf_ = nullptr;
};

TEST_F(UserDataOfARun, AFunctionCallKeepsItFromOneEvaluationToTheNext) {
  Run("module top; int x;\n"
      "  initial repeat (2) x = $fcount;\n"
      "endmodule\n");
  ExpectCounts({1, 2});
}

TEST_F(UserDataOfARun, ACallInAFunctionBodyKeepsItAcrossInvocations) {
  Run("module top; int x;\n"
      "  function int g; return $fcount; endfunction\n"
      "  initial begin x = g(); x = g(); end\n"
      "endmodule\n");
  ExpectCounts({1, 2});
}

TEST_F(UserDataOfARun, ACallInAClassMethodKeepsItAcrossInvocations) {
  Run("module top;\n"
      "  class C; static task m; $count; endtask endclass\n"
      "  initial begin C::m(); C::m(); end\n"
      "endmodule\n");
  ExpectCounts({1, 2});
}

TEST_F(UserDataOfARun, ACallInAProgramKeepsItAcrossInvocations) {
  Run("program p;\n"
      "  task t; $count; endtask\n"
      "  initial begin t; t; end\n"
      "endprogram\n");
  ExpectCounts({1, 2});
}

TEST_F(UserDataOfARun, DataPutByTheCompiletfIsReadByTheCalltf) {
  Run("module top; initial $mark; endmodule\n");
  EXPECT_EQ(read_in_calltf, &compiletf_marker);
}

TEST_F(UserDataOfARun, TwoHandlesToOneCallSeeEachOthersData) {
  Run("module top; initial $count; endmodule\n");
  ASSERT_NE(LastCall(), nullptr);
  void* through_calltf = vpi_get_userdata(LastCall());
  ASSERT_NE(through_calltf, nullptr);
  vpiHandle initial = ObjectsOf(vpiProcess, By("top")).at(0);
  vpiHandle iterated = vpi_handle(vpiStmt, initial);
  ASSERT_NE(iterated, nullptr);
  ASSERT_EQ(vpi_get(vpiType, iterated), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_userdata(iterated), through_calltf);
  int other = 0;
  ASSERT_EQ(vpi_put_userdata(iterated, &other), 1);
  EXPECT_EQ(vpi_get_userdata(LastCall()), &other);
}

TEST_F(UserDataOfARun, ARestartClearsTheDataOfACallOfTheDesign) {
  Run("module top; initial $count; endmodule\n");
  ASSERT_NE(LastCall(), nullptr);
  ASSERT_NE(vpi_get_userdata(LastCall()), nullptr);
  vpi_.DispatchRestart();
  EXPECT_EQ(vpi_get_userdata(LastCall()), nullptr);
}

TEST_F(UserDataOfARun, AResetClearsTheDataOfACallOfTheDesign) {
  Run("module top; initial $count; endmodule\n");
  ASSERT_NE(LastCall(), nullptr);
  ASSERT_NE(vpi_get_userdata(LastCall()), nullptr);
  vpi_.DispatchReset();
  EXPECT_EQ(vpi_get_userdata(LastCall()), nullptr);
}

TEST_F(UserDataOfARun, ARegistrationHandleHoldsNone) {
  int marker = 0;
  EXPECT_EQ(vpi_put_userdata(count_systf_, &marker), 0);
  const PLI_INT32 kPutError = vpi_chk_error(nullptr);
  EXPECT_EQ(kPutError, vpiError);
  EXPECT_EQ(vpi_get_userdata(count_systf_), nullptr);
}

}  // namespace
}  // namespace delta
