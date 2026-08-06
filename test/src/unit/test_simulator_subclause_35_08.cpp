#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"

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

}  // namespace
