#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.37.2 covers the vlog_startup_routines[] array as the means of
// initializing system task and system function callbacks, and of performing
// any other desired task, just after the simulator is invoked. The walking
// mechanism itself (a null-terminated array of void(*)() entries) is provided
// by §36.9.1, the startup tool-phase by §36.10.2, and vpi_register_systf()/
// vpi_register_cb() by §38.37.1/§38.36. These tests observe that existing
// machinery realizing §38.37.2's distinctive requirements: the array's stated
// purpose is registering system tasks and system functions, and a routine in
// it may equally perform any other desired task, such as installing a
// simulation callback.

class VlogStartupArrayInitialization : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

namespace {

// A single registration routine that, like the listnets_register/my_random_init
// examples referenced by §38.37.2, registers both a user-defined system task
// and a user-defined system function that appear in a compiled description.
void RegisterTaskAndFunction() {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$list_nets";
  vpi_register_systf(&task);

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.tfname = "$my_random";
  vpi_register_systf(&func);
}

int ReportCpuAtEnd(VpiCbData*) { return 0; }

// A routine that performs "any other desired task" rather than registering a
// system task or function: it installs an end-of-simulation callback, mirroring
// the setup_report_cpu() example that motivates §38.37.
void InstallEndOfSimulationCallback() {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &ReportCpuAtEnd;
  vpi_register_cb(&cb);
}

}  // namespace

// §38.37.2: the array of C functions is for registering system tasks and
// system functions; user-defined tasks and functions appearing in a compiled
// description are registered by a routine placed in vlog_startup_routines[].
// Walking such an array therefore leaves both the task and the function
// registered and retrievable by their source-level names.
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

// §38.37.2: the same array also provides a means of initializing callbacks and
// of performing any other desired task just after the simulator is invoked. A
// startup routine that installs a simulation callback rather than a systf is a
// legitimate use of the array, so walking it leaves that callback registered.
TEST_F(VlogStartupArrayInitialization, ArrayPerformsAnyOtherDesiredTask) {
  VlogStartupRoutine routines[] = {
      &InstallEndOfSimulationCallback,
      nullptr,
  };

  InvokeVlogStartupRoutines(routines);

  // No system task or function was registered; the desired task here was the
  // callback installation alone.
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
  ASSERT_EQ(vpi_ctx_.RegisteredCallbacks().size(), 1u);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].reason, cbEndOfSimulation);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks()[0].cb_rtn, &ReportCpuAtEnd);
}

// §38.37.2: "A tool vendor shall supply a file that contains the
// vlog_startup_routines array", and the array definition it shall be supplied
// with is "void (*vlog_startup_routines[]) ();". The symbol this test names is
// the one src/simulator/vlog_startup_routines.cpp supplies, reached through the
// extern "C" declaration in simulator/vpi_globals.h, so a tool that supplied no
// such file would not link this test at all. What is left to check is the type:
// an array of pointers to functions taking no arguments and returning nothing.
TEST_F(VlogStartupArrayInitialization, ToolSuppliesTheArrayTheStandardDefines) {
  EXPECT_TRUE(
      (std::is_same_v<std::remove_extent_t<decltype(vlog_startup_routines)>,
                      void (*)()>));
}

// §38.37.2: "Entries in the array shall be added by the user." The array the
// tool supplies therefore holds nothing but the null terminator that ends it,
// leaving every entry in it one somebody added to the vendor-supplied file: the
// tool registers no system task, system function or callback of its own behind
// a PLI application's back. Walking what is shipped registers nothing.
TEST_F(VlogStartupArrayInitialization, SuppliedArrayHoldsOnlyItsTerminator) {
  EXPECT_EQ(vlog_startup_routines[0], nullptr);

  InvokeVlogStartupRoutines(vlog_startup_routines);

  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
  EXPECT_TRUE(vpi_ctx_.RegisteredCallbacks().empty());
}

}  // namespace
}  // namespace delta
