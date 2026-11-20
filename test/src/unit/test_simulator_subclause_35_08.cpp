#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_reported_error.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(DpiExportedTask, ImportedFunctionCallingExportedTaskIsRejected) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_func_import", sc);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kFunctionCallsTask);
}

TEST(DpiExportedTask, ImportedContextTaskCallingExportedTaskIsAllowed) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  bool ran = false;
  task_export.impl = [&ran](const std::vector<DpiArgValue>&) -> DpiArgValue {
    ran = true;
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_task_import", sc, true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(ran);
}

TEST(DpiExportedTask, ImportedFunctionCallingExportedFunctionIsAllowed) {
  DpiRuntime rt;
  DpiRtExport func_export;
  func_export.c_name = "c_func";
  func_export.sv_name = "sv_func";
  func_export.is_task = false;
  rt.RegisterExport(func_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_func_import", sc);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_func", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
}

TEST(DpiExportedTask,
     NoncontextFunctionCallingExportedTaskIsRejectedByTaskRule) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  rt.RegisterExport(task_export);

  rt.EnterNoncontextImportCall("nonctx_func_import");

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kFunctionCallsTask);
}

TEST(DpiExportedTask, InnermostFunctionFrameInChainRootedAtTaskIsRejected) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("task_root", sc, true);
  rt.EnterContextImportCall("func_inner", sc, false);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kFunctionCallsTask);
}

TEST(DpiExportedTask, InnermostTaskFrameInChainRootedAtFunctionIsAllowed) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  bool ran = false;
  task_export.impl = [&ran](const std::vector<DpiArgValue>&) -> DpiArgValue {
    ran = true;
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("func_root", sc, false);
  rt.EnterContextImportCall("task_inner", sc, true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(ran);
}

TEST(DpiExportedTask, AnExportedTaskYieldsZeroWithNoDisableActive) {
  DpiSetCurrentDisabledState(false);
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  task_export.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(77);
  };
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_task_import", sc, true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 0);
}

TEST(DpiExportedTask, AnExportedTaskYieldsOneWhenADisableIsActiveOnReturn) {
  DpiSetCurrentDisabledState(false);
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  task_export.impl = [&rt](const std::vector<DpiArgValue>&) -> DpiArgValue {
    rt.ReturnFromExportUnderDisable(DpiDisableTarget::kAncestor);
    return DpiArgValue::FromInt(77);
  };
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_task_import", sc, true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 1);
  DpiSetCurrentDisabledState(false);
}

TEST(DpiExportedTask, AnExportedFunctionYieldsWhatItsBodyReturned) {
  DpiSetCurrentDisabledState(false);
  DpiRuntime rt;
  DpiRtExport func_export;
  func_export.c_name = "c_func";
  func_export.sv_name = "sv_func";
  func_export.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(77);
  };
  rt.RegisterExport(func_export);

  DpiScope sc;
  sc.name = "top";
  rt.EnterContextImportCall("ctx_func_import", sc);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_func", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 77);
}

TEST(DpiExportedTask, NoncontextTaskImportCallingExportedTaskIsRejected) {
  DpiSetCurrentDisabledState(false);
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  bool ran = false;
  task_export.impl = [&ran](const std::vector<DpiArgValue>&) -> DpiArgValue {
    ran = true;
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(task_export);

  rt.EnterNoncontextImportCall("plain_task_import", true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kNoncontextChain);
  EXPECT_FALSE(ran);
}

using ExportedTask = int (*)(int);
using ExportedTaskNoArgs = int (*)();

ExportedTask TaskNamed(const char* name) {
  return reinterpret_cast<ExportedTask>(dlsym(RTLD_DEFAULT, name));
}

ExportedTaskNoArgs TaskWithNoArgsNamed(const char* name) {
  return reinterpret_cast<ExportedTaskNoArgs>(dlsym(RTLD_DEFAULT, name));
}

int WaitTwice(int n) {
  ExportedTask sv_wait = TaskNamed("sv_wait");
  if (sv_wait == nullptr) return 0;
  sv_wait(n);
  sv_wait(n);
  return 0;
}

int StepOnce() {
  ExportedTaskNoArgs tick = TaskWithNoArgsNamed("tick");
  if (tick != nullptr) tick();
  return 0;
}

int DelayOnce(int d) {
  ExportedTask sv_delay = TaskNamed("sv_delay");
  if (sv_delay != nullptr) sv_delay(d);
  return 0;
}

int g_disabled_return = -1;
int g_disabled_state = -1;

int RunUntilDisabled() {
  ExportedTaskNoArgs sv_long = TaskWithNoArgsNamed("sv_long");
  if (sv_long == nullptr) return 0;
  g_disabled_return = sv_long();
  g_disabled_state = svIsDisabledState();
  if (g_disabled_state != 0) svAckDisabledState();
  return g_disabled_state;
}

int g_plain_return = -1;

int RunToCompletion() {
  ExportedTaskNoArgs sv_short = TaskWithNoArgsNamed("sv_short");
  if (sv_short == nullptr) return 0;
  g_plain_return = sv_short();
  return 0;
}

int TickByCName() {
  ExportedTaskNoArgs c_tick = TaskWithNoArgsNamed("c_tick");
  if (c_tick == nullptr) return 0;
  c_tick();
  return 0;
}

int UnexportedTaskHasNoSymbol() {
  return dlsym(RTLD_DEFAULT, "sv_never_exported_t") == nullptr ? 0 : 1;
}

int g_task_scopes = -1;

int ScopeOfCaller() {
  const char* name = svGetNameFromScope(svGetScope());
  if (name == nullptr) return 0;
  std::string_view path(name);
  if (path == "top.u1") g_task_scopes = (g_task_scopes * 10) + 1;
  if (path == "top.u2") g_task_scopes = (g_task_scopes * 10) + 2;
  return 0;
}

int EnableInBothInstances() {
  ExportedTaskNoArgs sv_note = TaskWithNoArgsNamed("sv_note");
  if (sv_note == nullptr) return 0;
  g_task_scopes = 0;
  svSetScope(svGetScopeFromName("top.u1"));
  sv_note();
  svSetScope(svGetScopeFromName("top.u2"));
  sv_note();
  return 0;
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiExportedTaskFromC, AnExportedTaskConsumesTimeForTheEnablingProcess) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" task sv_wait;\n"
      "  import \"DPI-C\" context task c_task(input int n);\n"
      "  task sv_wait(input int n); #n; endtask\n"
      "  int t0, t1;\n"
      "  initial begin t0 = $time; c_task(7); t1 = $time; end\n"
      "endmodule\n",
      f, {{"c_task", reinterpret_cast<void*>(&WaitTwice)}},
      "subclause_35_08_export_task_time");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "t0"), 0U);
  EXPECT_EQ(VariableValue(f, "t1"), 14U);
}

TEST(DpiExportedTaskFromC, AnImportedTaskEnabledFromANativeTask) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  int n = 0;\n"
      "  export \"DPI-C\" task tick;\n"
      "  import \"DPI-C\" context task c_step();\n"
      "  task tick(); #3 n++; endtask\n"
      "  task run(); c_step(); endtask\n"
      "  int ta, na, tb, nb;\n"
      "  initial begin\n"
      "    run(); ta = $time; na = n;\n"
      "    run(); tb = $time; nb = n;\n"
      "  end\n"
      "endmodule\n",
      f, {{"c_step", reinterpret_cast<void*>(&StepOnce)}},
      "subclause_35_08_import_task_in_task");
  EXPECT_EQ(VariableValue(f, "ta"), 3U);
  EXPECT_EQ(VariableValue(f, "na"), 1U);
  EXPECT_EQ(VariableValue(f, "tb"), 6U);
  EXPECT_EQ(VariableValue(f, "nb"), 2U);
}

TEST(DpiExportedTaskFromC, ImportedTasksInJoinNoneBranchesRunApart) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  int n = 0;\n"
      "  export \"DPI-C\" task sv_delay;\n"
      "  import \"DPI-C\" context task c_bg(input int d);\n"
      "  task sv_delay(input int d); #d n++; endtask\n"
      "  int t0, n0, t1, n1;\n"
      "  initial begin\n"
      "    fork c_bg(9); c_bg(4); join_none\n"
      "    t0 = $time; n0 = n;\n"
      "    wait (n == 2);\n"
      "    t1 = $time; n1 = n;\n"
      "  end\n"
      "endmodule\n",
      f, {{"c_bg", reinterpret_cast<void*>(&DelayOnce)}},
      "subclause_35_08_import_task_join_none");
  EXPECT_EQ(VariableValue(f, "t0"), 0U);
  EXPECT_EQ(VariableValue(f, "n0"), 0U);
  EXPECT_EQ(VariableValue(f, "t1"), 9U);
  EXPECT_EQ(VariableValue(f, "n1"), 2U);
}

TEST(DpiExportedTaskFromC, ADisableReturnsOneFromTheExportedTask) {
  g_disabled_return = -1;
  g_disabled_state = -1;
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" task sv_long;\n"
      "  import \"DPI-C\" context task c_disabled();\n"
      "  task sv_long(); #100; endtask\n"
      "  int t;\n"
      "  initial begin\n"
      "    fork begin : blk c_disabled(); end join_none\n"
      "    #5 disable blk;\n"
      "    t = $time;\n"
      "  end\n"
      "endmodule\n",
      f, {{"c_disabled", reinterpret_cast<void*>(&RunUntilDisabled)}},
      "subclause_35_08_export_task_disable");
  EXPECT_EQ(g_disabled_return, 1);
  EXPECT_EQ(g_disabled_state, 1);
  EXPECT_EQ(VariableValue(f, "t"), 5U);
}

TEST(DpiExportedTaskFromC, AnExportedTaskReturnsZeroWithNoDisable) {
  g_plain_return = -1;
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  int n = 0;\n"
      "  export \"DPI-C\" task sv_short;\n"
      "  import \"DPI-C\" context task c_plain();\n"
      "  task sv_short(); #2 n = 5; endtask\n"
      "  int t;\n"
      "  initial begin c_plain(); t = $time; end\n"
      "endmodule\n",
      f, {{"c_plain", reinterpret_cast<void*>(&RunToCompletion)}},
      "subclause_35_08_export_task_no_disable");
  EXPECT_EQ(g_plain_return, 0);
  EXPECT_EQ(VariableValue(f, "n"), 5U);
  EXPECT_EQ(VariableValue(f, "t"), 2U);
}

TEST(DpiExportedTaskFromC, ANoncontextImportedTaskEnablingAnExportIsAnError) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  int n = 0;\n"
      "  export \"DPI-C\" task sv_short;\n"
      "  import \"DPI-C\" task c_plain();\n"
      "  task sv_short(); #2 n = 5; endtask\n"
      "  initial c_plain();\n"
      "endmodule\n",
      f, {{"c_plain", reinterpret_cast<void*>(&RunToCompletion)}},
      "subclause_35_08_noncontext_task");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "exported subroutine 'sv_short' called from "
                            "imported subroutine 'c_plain', which is not "
                            "declared context",
                            0, "35.5.3"));
  EXPECT_EQ(VariableValue(f, "n"), 0U);
}

TEST(DpiExportedTaskFromC, AnExportedTaskIsEnabledByItsCIdentifier) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  int n = 0;\n"
      "  export \"DPI-C\" c_tick = task tick;\n"
      "  import \"DPI-C\" context task c_step();\n"
      "  task tick(); #3 n = n + 4; endtask\n"
      "  initial c_step();\n"
      "endmodule\n",
      f, {{"c_step", reinterpret_cast<void*>(&TickByCName)}},
      "subclause_35_08_export_task_c_identifier");
  EXPECT_EQ(VariableValue(f, "n"), 4U);
}

TEST(DpiExportedTaskFromC, ATaskWithoutAnExportHasNoSymbol) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  task sv_never_exported_t(); endtask\n"
      "  import \"DPI-C\" context function int probe();\n"
      "  int r = 7;\n"
      "  initial r = probe();\n"
      "endmodule\n",
      f, {{"probe", reinterpret_cast<void*>(&UnexportedTaskHasNoSymbol)}},
      "subclause_35_08_no_task_export");
  EXPECT_EQ(VariableValue(f, "r"), 0U);
}

TEST(DpiExportedTaskFromC, AnExportedTaskRunsInTheContextOfItsInstance) {
  g_task_scopes = -1;
  SimFixture f;
  RunWithImportsBound(
      "module m;\n"
      "  export \"DPI-C\" task sv_note;\n"
      "  import \"DPI-C\" context task where_now();\n"
      "  task sv_note(); where_now(); endtask\n"
      "endmodule\n"
      "module top;\n"
      "  import \"DPI-C\" context task both();\n"
      "  m u1();\n"
      "  m u2();\n"
      "  initial both();\n"
      "endmodule\n",
      f,
      {{"both", reinterpret_cast<void*>(&EnableInBothInstances)},
       {"where_now", reinterpret_cast<void*>(&ScopeOfCaller)}},
      "subclause_35_08_export_task_context");
  EXPECT_EQ(g_task_scopes, 12);
}

TEST(DpiExportedTaskInADesign, AnExportedTaskEnabledFromSvRunsAsBefore) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n = 0;\n"
      "  int at;\n"
      "  task bump(input int by, output int when);\n"
      "    #4 n = n + by;\n"
      "    when = $time;\n"
      "  endtask\n"
      "  export \"DPI-C\" task bump;\n"
      "  initial bump(6, at);\n"
      "endmodule\n",
      f, "at");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
  EXPECT_EQ(VariableValue(f, "n"), 6U);
}

}  // namespace
