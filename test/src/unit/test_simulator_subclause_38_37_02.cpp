#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <type_traits>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "simulator/foreign_code.h"
#include "simulator/shared_library.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VlogStartupArrayInitialization : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

namespace {

void RegisterTaskAndFunction() {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$list_nets");
  vpi_register_systf(&task);

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$my_random");
  vpi_register_systf(&func);
}

int ReportCpuAtEnd(s_cb_data*) { return 0; }

void InstallEndOfSimulationCallback() {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &ReportCpuAtEnd;
  vpi_register_cb(&cb);
}

}  // namespace

TEST_F(VlogStartupArrayInitialization, ArrayRegistersUserTasksAndFunctions) {
  VlogStartupRoutine routines[] = {
      &RegisterTaskAndFunction,
      nullptr,
  };

  InvokeVlogStartupRoutines(routines);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2u);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$list_nets");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[1].tfname, "$my_random");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

TEST_F(VlogStartupArrayInitialization, ArrayPerformsAnyOtherDesiredTask) {
  VlogStartupRoutine routines[] = {
      &InstallEndOfSimulationCallback,
      nullptr,
  };

  InvokeVlogStartupRoutines(routines);

  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
  ASSERT_EQ(vpi_ctx_.RegisteredCallbacks().size(), 1u);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].reason, cbEndOfSimulation);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].cb_rtn, &ReportCpuAtEnd);
}

TEST_F(VlogStartupArrayInitialization, ToolSuppliesTheArrayTheStandardDefines) {
  EXPECT_TRUE(
      (std::is_same_v<std::remove_extent_t<decltype(vlog_startup_routines)>,
                      void (*)()>));
}

TEST_F(VlogStartupArrayInitialization, SuppliedArrayHoldsOnlyItsTerminator) {
  EXPECT_EQ(vlog_startup_routines[0], nullptr);

  InvokeVlogStartupRoutines(vlog_startup_routines);

  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
  EXPECT_TRUE(vpi_ctx_.RegisteredCallbacks().empty());
}

constexpr std::string_view kStartupLibrary =
    "static int started = 0;\n"
    "static void count_start(void) { ++started; }\n"
    "void (*vlog_startup_routines[])(void) = {count_start, 0};\n"
    "int deltahdl_startup_count(void) { return started; }\n";

constexpr std::string_view kPlainLibrary =
    "int deltahdl_plain_marker(void) { return 1; }\n";

std::string BuiltLibrary(const ScratchDir& scratch, std::string_view name,
                         std::string_view source) {
  const std::string kBase = (scratch.dir / std::string(name)).string();
  const std::string kError = BuildCSharedLibrary(source, kBase, "cc");
  EXPECT_TRUE(kError.empty()) << kError;
  return kBase;
}

TEST(LoadedApplicationStartupRoutines, AreCalledWhenTheLibraryLoads) {
  ScratchDir scratch;
  const std::string kLibrary =
      BuiltLibrary(scratch, "deltahdl_startup_app", kStartupLibrary);
  SourceManager mgr;
  DiagEngine diag(mgr);
  ASSERT_TRUE(ForeignCodeLoadLibraries({}, {kLibrary}, diag));
  auto* count =
      reinterpret_cast<int (*)()>(GlobalSymbol("deltahdl_startup_count"));
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count(), 1);
}

TEST(LoadedApplicationStartupRoutines, ALibraryWithoutTheArrayLoadsAsBefore) {
  ScratchDir scratch;
  const std::string kLibrary =
      BuiltLibrary(scratch, "deltahdl_plain_app", kPlainLibrary);
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_TRUE(ForeignCodeLoadLibraries({}, {kLibrary}, diag));
  EXPECT_TRUE(diag.Diagnostics().empty());
}

}  // namespace
}  // namespace delta
