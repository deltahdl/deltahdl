#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.8.4: the sizetf, compiletf, and calltf application routines all take a
// single argument, and when the tool calls any of them it passes the value held
// in the registration's user_data field. These stubs record the lone argument
// each routine received so a test can confirm it is that user_data value. The
// three probes are kept distinct to show the rule holds uniformly across all
// three routines, not just one.
const char* g_sizetf_arg = nullptr;
const char* g_compiletf_arg = nullptr;
const char* g_calltf_arg = nullptr;

int RecordingSizetf(const char* arg) {
  g_sizetf_arg = arg;
  return 0;
}

int RecordingCompiletf(const char* arg) {
  g_compiletf_arg = arg;
  return 0;
}

int RecordingCalltf(const char* arg) {
  g_calltf_arg = arg;
  return 0;
}

void ResetArgProbes() {
  g_sizetf_arg = nullptr;
  g_compiletf_arg = nullptr;
  g_calltf_arg = nullptr;
}

// A VpiContext fixture so the round-trip tests can register a system function
// and read its record back, exercising the argument rule against the production
// registry rather than a bare struct.
class SystfApplicationRoutineArguments : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// -----------------------------------------------------------------------------
// §36.8.4: "The sizetf, compiletf, and calltf routines all take one argument."
// Each routine's type carries exactly one parameter; invoking any of them
// supplies precisely that single value and nothing more. The three routines
// share the one-argument shape uniformly.
// -----------------------------------------------------------------------------

TEST_F(SystfApplicationRoutineArguments,
       AllThreeRoutinesTakeTheOneUserDataArgument) {
  int payload = 0;

  VpiSystfData data = {};
  data.type = kVpiSysFunc;
  data.sysfunctype = kVpiSizedFunc;
  data.tfname = "$probe";
  data.sizetf = &RecordingSizetf;
  data.compiletf = &RecordingCompiletf;
  data.calltf = &RecordingCalltf;
  data.user_data = &payload;

  ResetArgProbes();
  VpiSystfInvoke(data.sizetf, data.user_data);
  VpiSystfInvoke(data.compiletf, data.user_data);
  VpiSystfInvoke(data.calltf, data.user_data);

  // The lone argument each routine receives is the registration's user_data.
  const char* expected = reinterpret_cast<const char*>(&payload);
  EXPECT_EQ(g_sizetf_arg, expected);
  EXPECT_EQ(g_compiletf_arg, expected);
  EXPECT_EQ(g_calltf_arg, expected);
}

// -----------------------------------------------------------------------------
// §36.8.4: the value passed is "the value supplied in the s_vpi_systf_data
// structure's user_data field when the user-defined system task or system
// function was registered." Registering the record and reading it back, then
// driving each stored routine, shows every routine receives that registered
// user_data - the field travels through the registry intact.
// -----------------------------------------------------------------------------

TEST_F(SystfApplicationRoutineArguments,
       RegisteredUserDataIsPassedToEachRoutine) {
  int payload = 0;

  VpiSystfData data = {};
  data.type = kVpiSysFunc;
  data.sysfunctype = kVpiSizedFunc;
  data.tfname = "$probe";
  data.sizetf = &RecordingSizetf;
  data.compiletf = &RecordingCompiletf;
  data.calltf = &RecordingCalltf;
  data.user_data = &payload;

  VpiHandle handle = vpi_ctx_.RegisterSystf(&data);
  ASSERT_NE(handle, nullptr);

  VpiSystfData read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.user_data, &payload);

  ResetArgProbes();
  VpiSystfInvoke(read_back.sizetf, read_back.user_data);
  VpiSystfInvoke(read_back.compiletf, read_back.user_data);
  VpiSystfInvoke(read_back.calltf, read_back.user_data);

  const char* expected = reinterpret_cast<const char*>(&payload);
  EXPECT_EQ(g_sizetf_arg, expected);
  EXPECT_EQ(g_compiletf_arg, expected);
  EXPECT_EQ(g_calltf_arg, expected);
}

// -----------------------------------------------------------------------------
// §36.8.4: there is exactly one user_data field, so all three routines of a
// single registration receive the very same value - not three independent
// arguments. Distinct registrations with distinct user_data are kept apart,
// confirming the argument is sourced from each record's own field.
// -----------------------------------------------------------------------------

TEST_F(SystfApplicationRoutineArguments,
       EachRegistrationSuppliesItsOwnUserData) {
  int payload_a = 0;
  int payload_b = 0;

  VpiSystfData task = {};
  task.type = kVpiSysTask;
  task.calltf = &RecordingCalltf;
  task.user_data = &payload_a;

  VpiSystfData func = {};
  func.type = kVpiSysFunc;
  func.calltf = &RecordingCalltf;
  func.user_data = &payload_b;

  ResetArgProbes();
  VpiSystfInvoke(task.calltf, task.user_data);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload_a));

  ResetArgProbes();
  VpiSystfInvoke(func.calltf, func.user_data);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload_b));
}

// -----------------------------------------------------------------------------
// §36.8.4: the argument is whatever value the registration supplied for
// user_data. When that field is left null (no user data was supplied at
// registration), the null is what each routine receives as its single argument
// - the routine is still called, just with a null user_data.
// -----------------------------------------------------------------------------

TEST_F(SystfApplicationRoutineArguments, NullUserDataIsPassedThroughUnchanged) {
  VpiSystfData data = {};
  data.type = kVpiSysFunc;
  data.sysfunctype = kVpiSizedFunc;
  data.sizetf = &RecordingSizetf;
  data.compiletf = &RecordingCompiletf;
  data.calltf = &RecordingCalltf;
  data.user_data = nullptr;

  ResetArgProbes();
  VpiSystfInvoke(data.sizetf, data.user_data);
  VpiSystfInvoke(data.compiletf, data.user_data);
  VpiSystfInvoke(data.calltf, data.user_data);

  EXPECT_EQ(g_sizetf_arg, nullptr);
  EXPECT_EQ(g_compiletf_arg, nullptr);
  EXPECT_EQ(g_calltf_arg, nullptr);
}

}  // namespace
}  // namespace delta
