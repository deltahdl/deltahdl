#include <gtest/gtest.h>

#include <array>
#include <string_view>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(DpiAndVpi, AnOpenArrayHandleIsNoVpiHandle) {
  EXPECT_FALSE(DpiOpenArrayHandleIsInterchangeableWithVpiHandle());
}

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

TEST(DpiAndVpi, EveryOtherVpiRoutineRequiresTheContextQualifier) {
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_handle"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_iterate"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_get_value"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_put_value"));
  EXPECT_TRUE(DpiVpiRoutineRequiresContext("vpi_register_cb"));
}

TEST(DpiAndVpi, SystemTaskActivitiesAreUnavailableAndIteratingModulesIsNot) {
  EXPECT_FALSE(DpiVpiActivityIsAvailableFromContextImport(
      DpiVpiActivity::kSystemTaskCallSiteHandle));
  EXPECT_FALSE(DpiVpiActivityIsAvailableFromContextImport(
      DpiVpiActivity::kSystemTaskCallback));
  EXPECT_TRUE(DpiVpiActivityIsAvailableFromContextImport(
      DpiVpiActivity::kIterateTopLevelModules));
}

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
      int tops = 0;
      vpiHandle it = vpi_iterate(vpiModule, nullptr);
      while (it != nullptr && vpi_scan(it) != nullptr) ++tops;
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

TEST_F(VpiFromAContextImport, TheImportScansTheTopModulesAndHasNoCallSite) {
  EXPECT_EQ(ScanFromTheImport(), 1);
}

}  // namespace
