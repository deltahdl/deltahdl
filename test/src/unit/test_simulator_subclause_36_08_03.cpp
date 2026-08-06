#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.8.3: a calltf application is the routine that performs the work of a
// user-defined system task or function each time it executes - for example,
// reading a test vector from the first task/function argument and assigning a
// value back to a second argument. These stubs record that the routine ran and
// the single argument it received, so a test can observe each execution.
const char* g_calltf_arg = nullptr;
int g_calltf_calls = 0;

int RecordingCalltf(const char* arg) {
  g_calltf_arg = arg;
  ++g_calltf_calls;
  return 0;
}

void ResetCalltfProbe() {
  g_calltf_arg = nullptr;
  g_calltf_calls = 0;
}

// A VpiContext fixture so the round-trip tests can register a system task or
// function and read its record back, exercising the calltf rule against the
// production registry rather than a bare struct.
class CalltfApplicationRoutine : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// -----------------------------------------------------------------------------
// §36.8.3: "A calltf VPI application routine shall be called each time the
// associated user-defined system task or system function is executed within the
// SystemVerilog source code." Unlike compiletf and sizetf, which run while the
// simulation data structure is compiled or built, calltf is an execution-time
// routine - it fires during simulation, not at build. That classification is
// the timing this subclause fixes for calltf.
// -----------------------------------------------------------------------------

TEST_F(CalltfApplicationRoutine, RunsAtExecutionTimeNotAtBuild) {
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

// -----------------------------------------------------------------------------
// §36.8.3: the routine is called "each time" the system task or function is
// executed. The subclause's worked example loops over $get_vector 1024 times
// and states the calltf routine is called that many times - i.e. once per
// execution, repeatedly. Driving the routine once for each execution of the
// loop reproduces that one-call-per-execution behavior.
// -----------------------------------------------------------------------------

TEST_F(CalltfApplicationRoutine, IsCalledOncePerExecution) {
  int payload = 0;

  VpiSystfData get_vector = {};
  get_vector.type = kVpiSysTask;
  get_vector.tfname = "$get_vector";
  get_vector.calltf = &RecordingCalltf;
  get_vector.user_data = &payload;

  ResetCalltfProbe();
  // Model the @(posedge clk) $get_vector(...) loop: each of the 1024 executions
  // drives the associated calltf application exactly once.
  const int kExecutions = 1024;
  for (int i = 0; i < kExecutions; ++i) {
    VpiSystfInvoke(get_vector.calltf, get_vector.user_data);
  }
  EXPECT_EQ(g_calltf_calls, kExecutions);
  // Every execution passes the registration's user_data as the lone argument.
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));
}

// -----------------------------------------------------------------------------
// §36.8.3: the rule covers "the associated user-defined system task or system
// function" - both kinds. The same calltf application runs whether the
// registration is a system task or a system function.
// -----------------------------------------------------------------------------

TEST_F(CalltfApplicationRoutine, RunsForBothSystemTaskAndSystemFunction) {
  int payload = 0;

  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.calltf = &RecordingCalltf;
  task.user_data = &payload;

  VpiSystfData func = {};
  func.type = kVpiSysFunc;
  func.calltf = &RecordingCalltf;
  func.user_data = &payload;

  ResetCalltfProbe();
  VpiSystfInvoke(task.calltf, task.user_data);
  EXPECT_EQ(g_calltf_calls, 1);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));

  ResetCalltfProbe();
  VpiSystfInvoke(func.calltf, func.user_data);
  EXPECT_EQ(g_calltf_calls, 1);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));
}

// -----------------------------------------------------------------------------
// §36.8.3: so that the routine can be called each time the system task or
// function executes, the registration preserves the supplied calltf
// application. The stored routine round-trips through the registry and, when
// driven for an execution, receives the registration's user_data as its lone
// argument.
// -----------------------------------------------------------------------------

TEST_F(CalltfApplicationRoutine, SuppliedRoutineRoundTripsAndReceivesUserData) {
  int payload = 0;

  VpiSystfData with_calltf = {};
  with_calltf.type = kVpiSysFunc;
  with_calltf.tfname = "$get_vector";
  with_calltf.calltf = &RecordingCalltf;
  with_calltf.user_data = &payload;

  VpiHandle handle = vpi_ctx_.RegisterSystf(&with_calltf);
  ASSERT_NE(handle, nullptr);

  VpiSystfData read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.calltf, &RecordingCalltf);

  ResetCalltfProbe();
  VpiSystfInvoke(read_back.calltf, read_back.user_data);
  EXPECT_EQ(g_calltf_calls, 1);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));
}

}  // namespace
}  // namespace delta
