#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.8.2: a compiletf application is typically used to check the correctness of
// the arguments a user-defined system task or function is given. These stubs
// record that they ran and what single argument they received, so a test can
// observe the routine actually being invoked.
const char* g_compiletf_arg = nullptr;
int g_compiletf_calls = 0;

int RecordingCompiletf(const char* arg) {
  g_compiletf_arg = arg;
  ++g_compiletf_calls;
  return 0;
}

void ResetCompiletfProbe() {
  g_compiletf_arg = nullptr;
  g_compiletf_calls = 0;
}

// A VpiContext fixture so the round-trip tests can register a system task or
// function and read its record back, exercising the optional-compiletf rule
// against the production registry rather than a bare struct.
class CompiletfApplicationRoutine : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// -----------------------------------------------------------------------------
// §36.8.2: "A compiletf VPI application routine shall be called when the
// user-defined system task or system function name is encountered during parsing
// or compiling the SystemVerilog source code." and "shall be called one time for
// each instance ... in the source description." The when of that call is
// delegated to §36.10.2 and §38.37.1; what §36.8.2 itself fixes is that compiletf
// runs while the design is being compiled/built - in contrast to calltf, which
// runs on every invocation during simulation. That compile-time-per-instance
// classification is what distinguishes compiletf from the execution-time routine.
// -----------------------------------------------------------------------------

TEST_F(CompiletfApplicationRoutine, IsACompileTimeRoutineUnlikeCalltf) {
  // compiletf fires while the simulation data structure is compiled/built...
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCompiletf));
  // ...whereas calltf fires per execution during simulation, not at compile time.
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

// -----------------------------------------------------------------------------
// §36.8.2: the routine is called when "the user-defined system task or system
// function name is encountered". Unlike sizetf (functions only, §36.8.1),
// compiletf applies to both kinds, so the same compiletf application runs whether
// the registration is a system task or a system function.
// -----------------------------------------------------------------------------

TEST_F(CompiletfApplicationRoutine, RunsForBothSystemTaskAndSystemFunction) {
  int payload = 0;

  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.compiletf = &RecordingCompiletf;
  task.user_data = &payload;

  VpiSystfData func = {};
  func.type = kVpiSysFunc;
  func.compiletf = &RecordingCompiletf;
  func.user_data = &payload;

  ResetCompiletfProbe();
  VpiSystfInvoke(task.compiletf, task.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  // The single argument passed is the registration's user_data, typed as char *.
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));

  ResetCompiletfProbe();
  VpiSystfInvoke(func.compiletf, func.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));
}

// -----------------------------------------------------------------------------
// §36.8.2: "Providing a compiletf routine is optional." A registration that
// supplies no compiletf application is accepted and reads back with no compiletf,
// and asking the runtime to run the absent routine is a harmless no-op.
// -----------------------------------------------------------------------------

TEST_F(CompiletfApplicationRoutine, IsOptional) {
  VpiSystfData no_compiletf = {};
  no_compiletf.type = kVpiSysTask;
  no_compiletf.tfname = "$check_args";
  no_compiletf.compiletf = nullptr;  // omitted - allowed

  VpiHandle handle = vpi_ctx_.RegisterSystf(&no_compiletf);
  ASSERT_NE(handle, nullptr);

  VpiSystfData read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  EXPECT_EQ(read_back.compiletf, nullptr);

  // Driving the missing routine does nothing and reports no result.
  ResetCompiletfProbe();
  EXPECT_EQ(VpiSystfInvoke(read_back.compiletf, read_back.user_data), 0);
  EXPECT_EQ(g_compiletf_calls, 0);
}

// -----------------------------------------------------------------------------
// §36.8.2: when a compiletf application is supplied, the registration preserves
// it so it can be called at compile time. The stored routine round-trips and,
// when invoked, receives the registration's user_data as its lone argument.
// -----------------------------------------------------------------------------

TEST_F(CompiletfApplicationRoutine, SuppliedRoutineRoundTripsAndReceivesUserData) {
  int payload = 0;

  VpiSystfData with_compiletf = {};
  with_compiletf.type = kVpiSysFunc;
  with_compiletf.tfname = "$get_vector";
  with_compiletf.compiletf = &RecordingCompiletf;
  with_compiletf.user_data = &payload;

  VpiHandle handle = vpi_ctx_.RegisterSystf(&with_compiletf);
  ASSERT_NE(handle, nullptr);

  VpiSystfData read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.compiletf, &RecordingCompiletf);

  ResetCompiletfProbe();
  VpiSystfInvoke(read_back.compiletf, read_back.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));
}

// -----------------------------------------------------------------------------
// §36.8.2: compiletf is called when "the user-defined system task or system
// function name is encountered" - so a supplied compiletf is preserved for a
// system task just as it is for a system function. Edge case complementing the
// function round-trip above and the task-without-compiletf case: a system task
// registered with a compiletf reads the routine back and runs it.
// -----------------------------------------------------------------------------

TEST_F(CompiletfApplicationRoutine, SystemTaskRegistrationPreservesCompiletf) {
  int payload = 0;

  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.tfname = "$record_event";
  task.compiletf = &RecordingCompiletf;
  task.user_data = &payload;

  VpiHandle handle = vpi_ctx_.RegisterSystf(&task);
  ASSERT_NE(handle, nullptr);

  VpiSystfData read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.compiletf, &RecordingCompiletf);

  ResetCompiletfProbe();
  VpiSystfInvoke(read_back.compiletf, read_back.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));
}

}  // namespace
}  // namespace delta
