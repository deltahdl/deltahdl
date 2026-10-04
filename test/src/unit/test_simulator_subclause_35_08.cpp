#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// §35.8: it is never legal to call an exported task from within an imported
// function. When the innermost import in the call chain is a function (the
// frame's is_task is false) and the export it tries to invoke names a task,
// the runtime rejects the call with kFunctionCallsTask, regardless of context.
TEST(DpiExportedTask, ImportedFunctionCallingExportedTaskIsRejected) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  // A context *function* import opens the chain (is_task defaults to false).
  rt.EnterContextImportCall("ctx_func_import", sc);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kFunctionCallsTask);
}

// §35.8: an imported *task* may call an exported task, provided it is declared
// context (§35.5.3). The function/task check must not reject a task caller, so
// a context task import reaches the export and the call is permitted.
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
  // A context task import (is_task = true) opens the chain.
  rt.EnterContextImportCall("ctx_task_import", sc, /*is_task=*/true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(ran);
}

// §35.8: the prohibition is specific to exported *tasks*. An imported function
// calling an exported *function* is unaffected by the §35.8 check and proceeds
// under the ordinary §35.5.3 rules.
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

// §35.8: the prohibition is independent of the chain's context property. Even a
// noncontext function import calling an exported task is rejected by the §35.8
// check, which runs ahead of the §35.5.3 noncontext check.
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

// §35.8: the prohibition is determined by the *immediate* caller of the export,
// i.e. the innermost import in the call chain — not the chain's root. A chain
// rooted at a task import but whose innermost frame is a function still cannot
// invoke an exported task.
TEST(DpiExportedTask, InnermostFunctionFrameInChainRootedAtTaskIsRejected) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  rt.RegisterExport(task_export);

  DpiScope sc;
  sc.name = "top";
  // Root frame is a task, but the innermost frame — the one actually issuing
  // the export call — is a function.
  rt.EnterContextImportCall("task_root", sc, /*is_task=*/true);
  rt.EnterContextImportCall("func_inner", sc, /*is_task=*/false);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kFunctionCallsTask);
}

// §35.8: conversely, when the innermost frame is a task the task rule does not
// fire even if an outer frame is a function. A context task issuing the call
// reaches the exported task, so it runs.
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
  // Root frame is a function, but the innermost frame issuing the call is a
  // context task.
  rt.EnterContextImportCall("func_root", sc, /*is_task=*/false);
  rt.EnterContextImportCall("task_inner", sc, /*is_task=*/true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_TRUE(ran);
}

// §35.8: "SystemVerilog tasks do not have return value types. The return value
// of an exported task is an int value that indicates if a disable is active or
// not on the current execution thread." With no disable active the call yields
// 0, whatever the registered body handed back — the body's value stands for no
// result the clause gives a task.
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
  rt.EnterContextImportCall("ctx_task_import", sc, /*is_task=*/true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 0);
}

// §35.8: and 1 where a disable is active on the thread when the exported task
// returns. §35.9 has the exported task's return set that state, which
// ReturnFromExportUnderDisable does, so the body below returns through it.
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
  rt.EnterContextImportCall("ctx_task_import", sc, /*is_task=*/true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  ASSERT_EQ(status, DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 1);
  DpiSetCurrentDisabledState(false);
}

// §35.8 gives the int result to exported tasks alone. An exported function has
// a return value type of its own, so its call yields what its body returned and
// the substitution above does not reach it.
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

// §35.8: "It is legal for an imported task to call an exported task only if the
// imported task is declared with the context property." The permitted case is
// covered above; this is the other half, where the task import is noncontext
// and the call is refused. The refusal is the §35.5.3 one, since the context
// property is what §35.8 defers to.
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

  rt.EnterNoncontextImportCall("plain_task_import", /*is_task=*/true);

  DpiArgValue result;
  auto status = rt.CallExportFromImport("sv_task", {}, &result);
  EXPECT_EQ(status, DpiExportCallStatus::kNoncontextChain);
  EXPECT_FALSE(ran);
}

// The exported task named `name` as C code in a loaded library reaches it: by
// its linkage name among the process's global symbols.
using ExportedTask = int (*)(int);
using ExportedTaskNoArgs = int (*)();

ExportedTask TaskNamed(const char* name) {
  return reinterpret_cast<ExportedTask>(dlsym(RTLD_DEFAULT, name));
}

ExportedTaskNoArgs TaskWithNoArgsNamed(const char* name) {
  return reinterpret_cast<ExportedTaskNoArgs>(dlsym(RTLD_DEFAULT, name));
}

// The imported tasks of the designs below: each calls an exported task that
// consumes time, once or twice, the last recording what §35.9 has a disable
// tell it.
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

// The value the design's variable `name` holds once the run is over, all ones
// where the run holds no such variable.
uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

// §35.8 with §35.5.1.5: an imported task may call an exported task that
// consumes time, and the process that enabled the import resumes once it has.
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

// §35.2.1: an imported task is enabled in statement context, a native task's
// body among them, and each enable consumes the exported task's time.
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

// §35.8 with §9.3.2: imported tasks enabled in join_none branches each consume
// the exported task's time on their own.
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

// §35.9: a disable reaching the process while it waits in an exported task
// returns 1 from that task to the C code, which sees the disabled state and
// acknowledges it, and the disabled block ends.
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

}  // namespace
