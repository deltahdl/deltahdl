#include <gtest/gtest.h>

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

}  // namespace
}  // namespace delta
