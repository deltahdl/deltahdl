#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.3.1 — Defining system task and system function names. Its whole rule is
// one sentence: "User-defined system task and system function names are defined
// using a system task and system function callback registry, which is part of
// the PLI mechanism." What the registry does with a registration handed to it
// is §36.9.1's, the clause saying so itself -- "Registering system tasks and
// system functions is described in 36.9.1" -- and is covered in that
// subclause's file. What is here is the other half: that registering a name is
// what defines it, so a design naming it reaches the application, and a design
// naming what no registration defines reaches nothing.
//
// §36.3.2's file beside this one takes the case where the name being defined is
// one a built-in already holds, which is a rule of its own. Every name here is
// nobody else's.
class DefiningSystfNames : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// How many times the registered task application below has been called, and by
// what value it was reached: the calltf is a plain C function, so a file-scope
// counter is where it can record that it ran.
int g_user_task_calls = 0;

int UserTaskCalltf(const char*) {
  ++g_user_task_calls;
  return 0;
}

// §38.37.1 with the call written in SystemVerilog: `$my_task;` in an initial
// block runs the application registered under that name. It ran nothing before:
// the registry was written and read back through vpi_get_systf_info and reached
// the evaluator by no route, so the call was reported under §20.1 as a name
// this tool does not implement.
TEST_F(DefiningSystfNames, RegisteredTaskIsCalledFromADesign) {
  g_user_task_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$my_task";
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

// A system function returns through the call handle §37.42 gives the
// application: vpi_handle(vpiSysTfCall, NULL) names the call being made, and
// vpi_put_value writes the value the function answers with. The design assigns
// the call to a variable, so what is asserted is the value the source sees.
int UserFuncCalltf(const char*) {
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
  func.tfname = "$my_func";
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

// The other half of the dispatch: a name no registration claims is still the
// name of nothing this tool implements, and §20.1's report stands. A dispatch
// that took an empty registry as a reason not to report would swallow the
// unknown name again.
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

// §36.3 has such a name "case sensitive", and §36.3.1 makes the registration
// what defines it, so what a registration defines is that spelling and not
// another. `$My_Task` is registered and `$my_task` is what the design names:
// two names, so the call reaches no application and §20.1's report stands. A
// registry matching without regard to case would run the application instead.
TEST_F(DefiningSystfNames, ADefinedNameIsCaseSensitive) {
  g_user_task_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$My_Task";
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
