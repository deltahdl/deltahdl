#include <gtest/gtest.h>

#include "fixture_simulator.h"
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

// -----------------------------------------------------------------------------
// §36.8.4: "When the tool calls these routines, it will pass to them the value
// supplied in the s_vpi_systf_data structure's user_data field when the
// user-defined system task or system function was registered."
//
// The tool's own calls are the subject, and every case above supplies the
// argument itself -- VpiSystfInvoke(read_back.sizetf, read_back.user_data)
// hands over what the case just read out of the registry, so what it observes
// is that a pointer passed to a function arrives at it. The cases below
// register the three routines and let a run reach them: the sizetf and the
// compiletf at §36.8's build period and the calltf at the execution of the
// call, three separate call sites in the tool, each of which has to find the
// user_data for itself.
// -----------------------------------------------------------------------------

// The user data the registrations below carry. An array rather than a string
// literal because user_data is a void* the application is handed back
// unchanged, and its address is what every case compares against.
char g_registered_user_data[] = "vector-reader";

// What each routine was handed, and whether it ran at all. The two are kept
// apart because null is a value the field can hold: without the flag, a routine
// the tool never called and a routine handed a null user_data leave the same
// trace behind.
const char* g_run_sizetf_arg = nullptr;
const char* g_run_compiletf_arg = nullptr;
const char* g_run_calltf_arg = nullptr;
bool g_run_sizetf_ran = false;
bool g_run_compiletf_ran = false;
bool g_run_calltf_ran = false;

int RunSizetf(const char* arg) {
  g_run_sizetf_arg = arg;
  g_run_sizetf_ran = true;
  return 8;
}

int RunCompiletf(const char* arg) {
  g_run_compiletf_arg = arg;
  g_run_compiletf_ran = true;
  return 0;
}

int RunCalltf(const char* arg) {
  g_run_calltf_arg = arg;
  g_run_calltf_ran = true;
  return 0;
}

void ResetRunProbes() {
  g_run_sizetf_arg = nullptr;
  g_run_compiletf_arg = nullptr;
  g_run_calltf_arg = nullptr;
  g_run_sizetf_ran = false;
  g_run_compiletf_ran = false;
  g_run_calltf_ran = false;
}

// Fills a registration of $probe carrying all three routines and `user_data`.
// It is a sized system function so that the sizetf is one of the three:
// §36.8.1 has that routine not called for a system task at all, which would
// leave a task-typed registration with two of the clause's three to show.
s_vpi_systf_data ProbeRegistration(void* user_data) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = "$probe";
  data.sizetf = &RunSizetf;
  data.compiletf = &RunCompiletf;
  data.calltf = &RunCalltf;
  data.user_data = user_data;
  return data;
}

// The design every case below runs: one call of $probe, which is enough to
// reach all three routines once each.
void RunOneProbeCall(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST_F(SystfApplicationRoutineArguments,
       TheToolHandsEachRoutineTheRegisteredUserData) {
  ResetRunProbes();
  s_vpi_systf_data data = ProbeRegistration(g_registered_user_data);
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  RunOneProbeCall(f);

  ASSERT_TRUE(g_run_sizetf_ran);
  ASSERT_TRUE(g_run_compiletf_ran);
  ASSERT_TRUE(g_run_calltf_ran);
  // Each was handed the very pointer the registration carried, rather than a
  // copy of the bytes, a null, or anything of the tool's own.
  EXPECT_EQ(g_run_sizetf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_compiletf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_calltf_arg, g_registered_user_data);
}

TEST_F(SystfApplicationRoutineArguments,
       TheValueIsTheOneThatStoodAtRegistration) {
  // §36.8.4 dates the value: it is the one supplied "when the user-defined
  // system task or system function was registered", so the application's own
  // structure is not where the tool reads it from afterwards. Here that
  // structure is written over between the registration and the run, and a tool
  // reading through to it would hand the routines the later pointer.
  char later_user_data[] = "written-afterwards";
  ResetRunProbes();
  s_vpi_systf_data data = ProbeRegistration(g_registered_user_data);
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  data.user_data = later_user_data;

  SimFixture f;
  RunOneProbeCall(f);

  EXPECT_EQ(g_run_sizetf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_compiletf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_calltf_arg, g_registered_user_data);
}

TEST_F(SystfApplicationRoutineArguments,
       TheToolHandsThroughANullUserDataUnchanged) {
  // §36.8.4 names no default: the argument is the value the field held, and a
  // registration that supplied none supplied null. Each routine still runs at
  // its own period and is handed that null, rather than being skipped or handed
  // something the tool made up -- which is what the three ran flags separate.
  ResetRunProbes();
  s_vpi_systf_data data = ProbeRegistration(nullptr);
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  RunOneProbeCall(f);

  ASSERT_TRUE(g_run_sizetf_ran);
  ASSERT_TRUE(g_run_compiletf_ran);
  ASSERT_TRUE(g_run_calltf_ran);
  EXPECT_EQ(g_run_sizetf_arg, nullptr);
  EXPECT_EQ(g_run_compiletf_arg, nullptr);
  EXPECT_EQ(g_run_calltf_arg, nullptr);
}

}  // namespace
}  // namespace delta
