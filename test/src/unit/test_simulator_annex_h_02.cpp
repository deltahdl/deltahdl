#include <gtest/gtest.h>

#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/dpi_side.h"

using namespace delta;

namespace {

TEST(DpiSubroutineKinds, TheFourKindsAreReadOffTheDeclaration) {
  DpiRtFunction imported_function;
  DpiRtFunction imported_task;
  imported_task.is_task = true;
  DpiRtExport exported_function;
  DpiRtExport exported_task;
  exported_task.is_task = true;
  EXPECT_EQ(DpiKindOf(imported_function), DpiSubroutineKind::kImportedFunction);
  EXPECT_EQ(DpiKindOf(imported_task), DpiSubroutineKind::kImportedTask);
  EXPECT_EQ(DpiKindOf(exported_function), DpiSubroutineKind::kExportedFunction);
  EXPECT_EQ(DpiKindOf(exported_task), DpiSubroutineKind::kExportedTask);
  EXPECT_EQ(DpiImplementingSide(imported_task), DpiSide::kForeign);
  EXPECT_EQ(DpiImplementingSide(exported_task), DpiSide::kSystemVerilog);
}

TEST(DpiSubroutineKinds, OnlyAnImportedTaskMayCallAnExportedTask) {
  EXPECT_TRUE(DpiKindMayCallExportedTask(DpiSubroutineKind::kImportedTask));
  EXPECT_FALSE(
      DpiKindMayCallExportedTask(DpiSubroutineKind::kImportedFunction));
  EXPECT_TRUE(DpiKindMayCallExportedTask(DpiSubroutineKind::kExportedTask));
  EXPECT_FALSE(
      DpiKindMayCallExportedTask(DpiSubroutineKind::kExportedFunction));
}

DpiExportCallStatus CallExportedTaskFromDeclaredImport(bool import_is_task) {
  DpiRuntime rt;
  DpiRtExport task_export;
  task_export.c_name = "c_task";
  task_export.sv_name = "sv_task";
  task_export.is_task = true;
  task_export.scope_name = "top";
  task_export.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterExport(task_export);

  DpiRtFunction import;
  import.c_name = "c_caller";
  import.sv_name = "sv_caller";
  import.is_context = true;
  import.is_task = import_is_task;
  import.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(import);

  DpiScope scope;
  scope.name = "top";
  rt.EnterDeclaredImportCall("sv_caller", scope);
  DpiArgValue result;
  return rt.CallExportFromImport("sv_task", {}, &result);
}

TEST(DpiSubroutineKinds, TheDeclarationSaysWhetherTheImportIsATask) {
  EXPECT_EQ(CallExportedTaskFromDeclaredImport(true), DpiExportCallStatus::kOk);
  EXPECT_EQ(CallExportedTaskFromDeclaredImport(false),
            DpiExportCallStatus::kFunctionCallsTask);
}

}  // namespace
