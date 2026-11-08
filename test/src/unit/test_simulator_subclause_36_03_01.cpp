#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class DefiningSystfNames : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

int g_user_task_calls = 0;

PLI_INT32 UserTaskCalltf(PLI_BYTE8*) {
  ++g_user_task_calls;
  return 0;
}

TEST_F(DefiningSystfNames, RegisteredTaskIsCalledFromADesign) {
  g_user_task_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$my_task");
  task.calltf = UserTaskCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $my_task;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(g_user_task_calls, 1);
  EXPECT_FALSE(f.diag.HasErrors());
}

PLI_INT32 UserFuncCalltf(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 42;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

TEST_F(DefiningSystfNames, RegisteredFunctionReturnsItsValueToTheDesign) {
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiSizedFunc;
  func.tfname = VpiText("$my_func");
  func.calltf = UserFuncCalltf;
  ASSERT_NE(vpi_register_systf(&func), nullptr);

  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  initial r = $my_func();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST_F(DefiningSystfNames, UnregisteredNameIsStillReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $no_such_task;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$no_such_task is not a system task or system function this tool "
      "implements",
      2, "20.1"));
}

TEST_F(DefiningSystfNames, ADefinedNameIsCaseSensitive) {
  g_user_task_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$My_Task");
  task.calltf = UserTaskCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $my_task;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(g_user_task_calls, 0);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$my_task is not a system task or system function this tool implements",
      2, "20.1"));
}

}  // namespace
}  // namespace delta
