#include <gtest/gtest.h>

#include <array>
#include <string_view>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

// §H.9.5: no specific relationship is defined between DPI and VPI, and a
// vpiHandle is not equivalent to an svOpenArrayHandle: the two may not be
// interchanged and passed between functions of the two interfaces.
TEST(DpiAndVpi, AnOpenArrayHandleIsNoVpiHandle) {
  EXPECT_FALSE(DpiOpenArrayHandleIsInterchangeableWithVpiHandle());
}

// §H.9.5: the VPI routines an import may call without the context qualifier
// are Table 36-9's exceptions -- the three vpi_printf-family I/O routines,
// the six vpi_mcd I/O routines and vpi_get_vlog_info -- since they do not
// access the Verilog model.
TEST(DpiAndVpi, TenVpiRoutinesNeedNoContextQualifier) {
  const std::array<std::string_view, 10> kExceptions =
      DpiVpiRoutinesCallableWithoutContext();
  EXPECT_EQ(kExceptions[0], "vpi_printf");
  EXPECT_EQ(kExceptions[1], "vpi_vprintf");
  EXPECT_EQ(kExceptions[2], "vpi_flush");
  EXPECT_EQ(kExceptions[3], "vpi_mcd_open");
  EXPECT_EQ(kExceptions[4], "vpi_mcd_close");
  EXPECT_EQ(kExceptions[5], "vpi_mcd_name");
  EXPECT_EQ(kExceptions[6], "vpi_mcd_printf");
  EXPECT_EQ(kExceptions[7], "vpi_mcd_vprintf");
  EXPECT_EQ(kExceptions[8], "vpi_mcd_flush");
  EXPECT_EQ(kExceptions[9], "vpi_get_vlog_info");
  for (std::string_view routine : kExceptions) {
    EXPECT_FALSE(DpiVpiRoutineRequiresContext(routine)) << routine;
  }
}

// §H.9.5: every other VPI function accesses the Verilog model and requires
// the import calling it to be flagged context.
TEST(DpiAndVpi, EveryOtherVpiRoutineRequiresTheContextQualifier) {
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_handle"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_iterate"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_get_value"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_put_value"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_register_cb"));
}

// §H.9.5: an imported subroutine is not a system task, so the handle to the
// system task call site and the callbacks and other activities associated
// with system tasks are not available from within a context import, while
// iterating the top-level modules is.
TEST(DpiAndVpi, SystemTaskActivitiesAreUnavailableAndIteratingModulesIsNot) {
  EXPECT_FALSE(DpiVpiActivityIsAvailableFromContextImport(
      DpiVpiActivity::kSystemTaskCallSiteHandle));
  EXPECT_FALSE(DpiVpiActivityIsAvailableFromContextImport(
      DpiVpiActivity::kSystemTaskCallback));
  EXPECT_TRUE(DpiVpiActivityIsAvailableFromContextImport(
      DpiVpiActivity::kIterateTopLevelModules));
}

// The clause's two calls made from within a context import under this tool:
// a VPI data model holding one top-level module, and a DpiRuntime whose
// context import scans the top-level modules and asks for the system task
// call site.
class VpiFromAContextImport : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&vpi_ctx_);
    VpiHandle top = vpi_ctx_.CreateModule("top", "top");
    top->top_module = true;

    DpiRtFunction scan;
    scan.sv_name = "scan_design";
    scan.is_context = true;
    scan.return_type = DataTypeKind::kInt;
    scan.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
      // Prepare to scan all top-level modules, and count what the scan yields.
      int tops = 0;
      vpiHandle it = vpi_iterate(vpiModule, nullptr);
      while (it != nullptr && vpi_scan(it) != nullptr) ++tops;
      // Get the handle to the system task call site, which no import has.
      vpiHandle call_site = vpi_handle(vpiSysTfCall, nullptr);
      return DpiArgValue::FromInt(call_site == nullptr ? tops : -1);
    };
    rt_.RegisterImport(scan);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  int ScanFromTheImport() {
    DpiScope decl_scope;
    decl_scope.name = "top";
    rt_.EnterContextImportCall("scan_design", decl_scope);
    DpiArgValue result = rt_.CallImport("scan_design", {});
    rt_.LeaveImportCall();
    return result.AsInt();
  }

  VpiContext vpi_ctx_;
  DpiRuntime rt_;
};

// §H.9.5: vpi_iterate(vpiModule, NULL) works reliably from within a context
// import, reaching the design's one top-level module, and
// vpi_handle(vpiSysTfCall, NULL) reaches no call site there, the import not
// being a system task.
TEST_F(VpiFromAContextImport, TheImportScansTheTopModulesAndHasNoCallSite) {
  EXPECT_EQ(ScanFromTheImport(), 1);
}

}  // namespace
