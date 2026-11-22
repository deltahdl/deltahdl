#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int control_op = vpiFinish;
int control_level = 0;
int armed_reason = cbAfterDelay;
SimContext* looked_at_run = nullptr;
bool ending_seen_in_routine = true;

PLI_INT32 ControlThenWriteCalltf(PLI_BYTE8*) {
  vpi_control(control_op, control_level);
  vpi_printf(VpiText("written after the call\n"));
  return 0;
}

PLI_INT32 ControlThenLook(p_cb_data) {
  vpi_control(control_op, 0);
  ending_seen_in_routine = looked_at_run->FinishRequested();
  return 0;
}

PLI_INT32 ControlThenLookCalltf(PLI_BYTE8*) { return ControlThenLook(nullptr); }

PLI_INT32 ArmCallbackCalltf(PLI_BYTE8*) {
  static s_vpi_time time = {};
  static s_vpi_value value = {};
  time.type = vpiSimTime;
  time.low = 1;
  value.format = vpiIntVal;
  s_cb_data cb = {};
  cb.reason = armed_reason;
  cb.cb_rtn = &ControlThenLook;
  cb.time = &time;
  cb.value = &value;
  if (armed_reason == cbValueChange) {
    cb.obj = vpi_handle_by_name(VpiText("top.trig"), nullptr);
  }
  vpi_register_cb(&cb);
  return 0;
}

class ControlOfARun : public VpiDesignRun {
 protected:
  void RegisterProbe(PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static std::string OneLineDesign(const std::string& action) {
    return "module top; initial begin #5 " + action +
           "; #5 $display(\"later\"); end endmodule\n";
  }

  std::string OutputOfControl(int op, int level) {
    control_op = op;
    control_level = level;
    RegisterProbe(&ControlThenWriteCalltf);
    vpi_.ConnectOutputChannel(&f_.ctx.Log().Out());
    testing::internal::CaptureStdout();
    Run(OneLineDesign("$probe"));
    vpi_.ConnectOutputChannel(nullptr);
    return testing::internal::GetCapturedStdout();
  }

  static std::string OutputOfTask(const std::string& task) {
    SimFixture f;
    testing::internal::CaptureStdout();
    RtlirDesign* design = ElaborateSrc(OneLineDesign(task), f);
    if (design != nullptr) LowerAndRun(design, f);
    return testing::internal::GetCapturedStdout();
  }

  void ExpectTheTasksOutput(int op, const std::string& task, int level) {
    const std::string kControlled = OutputOfControl(op, level);
    const std::string kTask =
        OutputOfTask(task + "(" + std::to_string(level) + ")");
    EXPECT_EQ(kControlled, "written after the call\n" + kTask);
  }

  int AfterOnceACallbackEndsTheRun(int op, int reason) {
    control_op = op;
    armed_reason = reason;
    looked_at_run = &f_.ctx;
    ending_seen_in_routine = true;
    RegisterProbe(&ArmCallbackCalltf);
    Run("module top; int after = 0; int trig = 0;\n"
        "  initial begin #1 $probe; #4 trig = 1; #5 after = 1; end\n"
        "endmodule\n");
    return IntegerOf(By("top.after"));
  }
};

TEST_F(ControlOfARun, AFinishAtLevelZeroPrintsWhatFinishZeroPrints) {
  ExpectTheTasksOutput(vpiFinish, "$finish", 0);
}

TEST_F(ControlOfARun, AFinishAtLevelOnePrintsWhatFinishOnePrints) {
  ExpectTheTasksOutput(vpiFinish, "$finish", 1);
}

TEST_F(ControlOfARun, AFinishAtLevelTwoPrintsWhatFinishTwoPrints) {
  ExpectTheTasksOutput(vpiFinish, "$finish", 2);
}

TEST_F(ControlOfARun, AStopAtLevelZeroPrintsWhatStopZeroPrints) {
  ExpectTheTasksOutput(vpiStop, "$stop", 0);
}

TEST_F(ControlOfARun, AStopAtLevelOnePrintsWhatStopOnePrints) {
  ExpectTheTasksOutput(vpiStop, "$stop", 1);
}

TEST_F(ControlOfARun, AStopAtLevelTwoPrintsWhatStopTwoPrints) {
  ExpectTheTasksOutput(vpiStop, "$stop", 2);
}

TEST_F(ControlOfARun, AStopActsOnceTheRoutineReturns) {
  control_op = vpiStop;
  looked_at_run = &f_.ctx;
  ending_seen_in_routine = true;
  RegisterProbe(&ControlThenLookCalltf);
  Run("module top; int after = 0;\n"
      "  initial begin #5 $probe; #5 after = 1; end\n"
      "endmodule\n");
  EXPECT_FALSE(ending_seen_in_routine);
  EXPECT_EQ(IntegerOf(By("top.after")), 0);
}

TEST_F(ControlOfARun, AFinishFromADelayCallbackEndsTheRunOnItsReturn) {
  EXPECT_EQ(AfterOnceACallbackEndsTheRun(vpiFinish, cbAfterDelay), 0);
  EXPECT_FALSE(ending_seen_in_routine);
  EXPECT_TRUE(f_.ctx.FinishRequested());
}

TEST_F(ControlOfARun, AFinishFromAValueChangeCallbackEndsTheRunOnItsReturn) {
  EXPECT_EQ(AfterOnceACallbackEndsTheRun(vpiFinish, cbValueChange), 0);
  EXPECT_FALSE(ending_seen_in_routine);
  EXPECT_TRUE(f_.ctx.FinishRequested());
}

TEST_F(ControlOfARun, AStopFromADelayCallbackStopsTheRunOnItsReturn) {
  EXPECT_EQ(AfterOnceACallbackEndsTheRun(vpiStop, cbAfterDelay), 0);
  EXPECT_FALSE(ending_seen_in_routine);
}

TEST_F(ControlOfARun, AStopFromAValueChangeCallbackStopsTheRunOnItsReturn) {
  EXPECT_EQ(AfterOnceACallbackEndsTheRun(vpiStop, cbValueChange), 0);
  EXPECT_FALSE(ending_seen_in_routine);
}

VpiHandle scope_seen_in_routine = nullptr;
std::string run_scope_seen_in_routine;

PLI_INT32 ScopeThenLookCalltf(PLI_BYTE8*) {
  vpi_control(vpiSetInteractiveScope,
              vpi_handle_by_name(VpiText("top.u"), nullptr));
  scope_seen_in_routine = GetGlobalVpiContext().InteractiveScope();
  run_scope_seen_in_routine = looked_at_run->InteractiveScope();
  return 0;
}

TEST_F(ControlOfARun, TheScopeChangesBeforeTheRoutineReturns) {
  looked_at_run = &f_.ctx;
  scope_seen_in_routine = nullptr;
  run_scope_seen_in_routine.clear();
  RegisterProbe(&ScopeThenLookCalltf);
  Run("module sub; endmodule\n"
      "module top; sub u(); initial #5 $probe; endmodule\n");
  ASSERT_NE(scope_seen_in_routine, nullptr);
  EXPECT_EQ(scope_seen_in_routine, VpiObjectOf(By("top.u")));
  EXPECT_EQ(run_scope_seen_in_routine, "top.u");
}

TEST_F(ControlOfARun, ShowScopesAndShowVarsReportTheNewScope) {
  looked_at_run = &f_.ctx;
  RegisterProbe(&ScopeThenLookCalltf);
  testing::internal::CaptureStdout();
  Run("module sub; int v = 3; if (1) begin : g int w = 4; end endmodule\n"
      "module top; int x = 1; sub u();\n"
      "  initial begin\n"
      "    $showscopes; $showvars; $display(\"--\");\n"
      "    #5 $probe; $showscopes; $showvars; $display(\"--\");\n"
      "    $scope(top.u); $showscopes; $showvars;\n"
      "  end\n"
      "endmodule\n");
  const std::string kOut = testing::internal::GetCapturedStdout();
  const std::size_t kFirst = kOut.find("--\n");
  ASSERT_NE(kFirst, std::string::npos);
  const std::size_t kSecond = kOut.find("--\n", kFirst + 3);
  ASSERT_NE(kSecond, std::string::npos);
  const std::string kBefore = kOut.substr(0, kFirst);
  const std::string kAfterControl =
      kOut.substr(kFirst + 3, kSecond - kFirst - 3);
  const std::string kAfterScopeTask = kOut.substr(kSecond + 3);
  EXPECT_NE(kAfterControl, kBefore);
  EXPECT_EQ(kAfterControl, kAfterScopeTask);
  EXPECT_NE(kAfterControl.find("v = "), std::string::npos);
}

TEST_F(ControlOfARun, EveryScopeClassKindBecomesTheScope) {
  Run("package pk; endpackage\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  ifc i0(); prg p0();\n"
      "  task tk; endtask\n"
      "  function int fn; return 0; endfunction\n"
      "  if (1) begin : g end\n"
      "  class C; endclass\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  initial fork : nf join\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::vector<std::pair<const char*, vpiHandle>> kScopes = {
      {"task", Named(vpiTask, top, "tk")},
      {"function", Named(vpiFunction, top, "fn")},
      {"generate scope", By("top.g")},
      {"named fork", By("top.nf")},
      {"interface instance", By("top.i0")},
      {"program instance", By("top.p0")},
      {"package", By("pk")},
      {"class defn", Named(vpiClassDefn, top, "C")},
      {"clocking block", Named(vpiClockingBlock, top, "cb")},
  };
  for (const auto& [kind, scope] : kScopes) {
    ASSERT_NE(scope, nullptr) << kind;
    EXPECT_EQ(vpi_control(vpiSetInteractiveScope, scope), 1) << kind;
    EXPECT_EQ(vpi_.InteractiveScope(), VpiObjectOf(scope)) << kind;
    EXPECT_EQ(f_.ctx.InteractiveScope(), vpi_get_str(vpiFullName, scope))
        << kind;
  }
}

}  // namespace
}  // namespace delta
