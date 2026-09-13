#include <gtest/gtest.h>

#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/dpi_side.h"

using namespace delta;

// Annex H.2 opens by listing the four kinds of subroutine the DPI admits:
// imported functions, functions implemented in C and given import
// declarations; exported functions and exported tasks, implemented in
// SystemVerilog and given export declarations; and imported tasks, functions
// implemented in C that can in turn call exported tasks. The cases check the
// kind the runtime's record of a declaration falls under, that an imported
// task is the kind that may call an exported task, and that a call chain
// opened from a declaration lets an imported task reach an exported task
// where an imported function, declared the same in every other way, is
// refused -- the frame taking the declaration's word, as it takes its context
// property, rather than the call site's.

namespace {

// §H.2: the four kinds, read off the import or export record.
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

// §H.2 with §35.8: an imported task may call exported tasks; an imported
// function may not.
TEST(DpiSubroutineKinds, OnlyAnImportedTaskMayCallAnExportedTask) {
  EXPECT_TRUE(DpiKindMayCallExportedTask(DpiSubroutineKind::kImportedTask));
  EXPECT_FALSE(
      DpiKindMayCallExportedTask(DpiSubroutineKind::kImportedFunction));
  EXPECT_TRUE(DpiKindMayCallExportedTask(DpiSubroutineKind::kExportedTask));
  EXPECT_FALSE(
      DpiKindMayCallExportedTask(DpiSubroutineKind::kExportedFunction));
}

// An exported task registered in the scope `top`, and a context import of
// the given kind registered beside it, with the chain opened from the
// import's declaration.
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

// §H.2: a chain opened from the declaration of an imported task lets it call
// an exported task, and one opened from the declaration of an imported
// function, context and scoped the same, is refused as a function calling a
// task; the declaration, not the call site, says which kind the import is.
TEST(DpiSubroutineKinds, TheDeclarationSaysWhetherTheImportIsATask) {
  EXPECT_EQ(CallExportedTaskFromDeclaredImport(/*import_is_task=*/true),
            DpiExportCallStatus::kOk);
  EXPECT_EQ(CallExportedTaskFromDeclaredImport(/*import_is_task=*/false),
            DpiExportCallStatus::kFunctionCallsTask);
}

}  // namespace
