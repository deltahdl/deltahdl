#include <gtest/gtest.h>

#include <array>
#include <cstdarg>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_dpi_scope_names.h"
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

class VpiFromADesignsImport : public VpiDesignRun {
 protected:
  void RunImport(const std::string& qualifier, int (*body)()) {
    std::string src = "module t;\n  import \"DPI-C\" ";
    src += qualifier;
    src += " function int from_c();\n  int r;\n  initial r = from_c();\n";
    src += "endmodule\n";
    RunDesignWithC(src, f_, {{"from_c", CAddress(body)}}, "annex_h_09_05");
  }
};

int CountTopModules() {
  int tops = 0;
  vpiHandle it = vpi_iterate(vpiModule, nullptr);
  while (it != nullptr && vpi_scan(it) != nullptr) ++tops;
  return tops;
}

int AskForTheCallSite() {
  vpiHandle call_site = vpi_handle(vpiSysTfCall, nullptr);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  SeeInC({call_site == nullptr, kLevel != 0});
  return 0;
}

PLI_INT32 AskForTheCallSiteInACalltf(PLI_BYTE8*) {
  vpiHandle call_site = vpi_handle(vpiSysTfCall, nullptr);
  const PLI_INT32 kLevel = vpi_chk_error(nullptr);
  SeeInC({call_site == nullptr, kLevel != 0});
  return 0;
}

PLI_BYTE8* TaskNameSeen() {
  static PLI_BYTE8 name[] = "$see_site";
  return name;
}

PLI_BYTE8* LateTaskName() {
  static PLI_BYTE8 name[] = "$late_task";
  return name;
}

int RegisterASystemTask() {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = LateTaskName();
  data.calltf = &AskForTheCallSiteInACalltf;
  vpiHandle registered = vpi_register_systf(&data);
  const PLI_INT32 kLevel = vpi_chk_error(nullptr);
  SeeInC({registered == nullptr, kLevel != 0});
  return 0;
}

PLI_INT32 NoteTheDelay(p_cb_data) {
  SeeInC({7});
  return 0;
}

int RegisterADelayCallback() {
  static s_vpi_time after;
  after.type = vpiSimTime;
  after.low = 1;
  s_cb_data data = {};
  data.reason = cbAfterDelay;
  data.cb_rtn = &NoteTheDelay;
  data.time = &after;
  SeeInC({vpi_register_cb(&data) != nullptr});
  return 0;
}

TEST_F(VpiFromADesignsImport, AContextImportIteratesTheTopModules) {
  RunImport("context", &CountTopModules);
  EXPECT_EQ(DesignValue(f_, "r"), 1u);
}

TEST_F(VpiFromADesignsImport, DISABLED_AskingForTheCallSiteIsAnError) {
  RunImport("context", &AskForTheCallSite);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1}));
}

TEST_F(VpiFromADesignsImport, ASystemTaskAskingForItsCallSiteIsNoError) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = TaskNameSeen();
  data.calltf = &AskForTheCallSiteInACalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  SeenInC().clear();
  Run("module t;\n"
      "  initial $see_site;\n"
      "endmodule\n");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0, 0}));
}

TEST_F(VpiFromADesignsImport, DISABLED_ASystemTaskIsNotRegisteredFromAnImport) {
  RunImport("context", &RegisterASystemTask);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1}));
}

TEST_F(VpiFromADesignsImport, ADelayCallbackIsRegisteredFromAContextImport) {
  RunImport("context", &RegisterADelayCallback);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 7}));
}

int PrintThroughV(const char* format, ...) {
  va_list args = {};
  va_start(args, format);
  std::string text = format;
  const int kWritten = vpi_vprintf(text.data(), args);
  va_end(args);
  return kWritten;
}

int PrintToChannelThroughV(PLI_UINT32 channel, const char* format, ...) {
  va_list args = {};
  va_start(args, format);
  std::string text = format;
  const int kWritten = vpi_mcd_vprintf(channel, text.data(), args);
  va_end(args);
  return kWritten;
}

int PrintAndFlush() {
  std::string format = "a%d";
  const int kPrinted = vpi_printf(format.data(), 5);
  const int kListed = PrintThroughV("b%d;", 12);
  SeeInC({kPrinted, kListed, vpi_flush()});
  return 0;
}

int UseAChannel() {
  std::string path = ::testing::TempDir();
  path += "annex_h_09_05_channel.txt";
  const PLI_UINT32 kChannel = vpi_mcd_open(path.data());
  const char* name = vpi_mcd_name(kChannel);
  std::string format = "c%d";
  SeeInC({kChannel != 0, name != nullptr && path == name,
          vpi_mcd_printf(kChannel, format.data(), 34),
          PrintToChannelThroughV(kChannel, "d%d", 567), vpi_mcd_flush(kChannel),
          vpi_mcd_close(kChannel)});
  return 0;
}

int ReadTheVlogInfo() {
  s_vpi_vlog_info info = {};
  SeeInC({vpi_get_vlog_info(&info), info.product != nullptr,
          info.version != nullptr});
  return 0;
}

TEST_F(VpiFromADesignsImport, ANoncontextImportPrintsAndFlushes) {
  RunImport("", &PrintAndFlush);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{2, 4, 0}));
  EXPECT_EQ(vpi_.LogFileFlushed(), "a5b12;");
}

TEST_F(VpiFromADesignsImport, ANoncontextImportUsesAChannel) {
  RunImport("", &UseAChannel);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, 3, 4, 0, 0}));
}

TEST_F(VpiFromADesignsImport, ANoncontextImportReadsTheToolInformation) {
  RunImport("", &ReadTheVlogInfo);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, 1}));
}

}  // namespace
