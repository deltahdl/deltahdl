#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
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

// -----------------------------------------------------------------------------
// §36.8.3: "A calltf VPI application routine shall be called each time the
// associated user-defined system task or system function is executed within the
// SystemVerilog source code", and the clause's example is one call site inside
// a loop: "the following SystemVerilog loop would call the calltf routine that
// is associated with the $get_vector user-defined system task name 1024 times".
// So what the rule counts is executions, and not the one call the source
// description wrote -- which is the count §36.8.2's compiletf answers with.
//
// Every case above drives the routine by hand, which says nothing about what a
// running design does with it. These run one.
// -----------------------------------------------------------------------------

// What the applications below recorded across a whole run. A calltf is a plain
// C function with no return path to the case that provoked it, so file scope is
// the only place it has to leave a count.
int g_calltf_runs = 0;
int g_compiletf_runs = 0;
uint64_t g_arg_total = 0;

// Counts its own executions and adds up the first argument as it stood at each
// one. The total is what separates one execution from many even where the count
// does not: a run that built the call once and reused it adds the same value
// every time.
int CountingCalltf(const char*) {
  ++g_calltf_runs;
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  vpiHandle arg = vpi_scan(args);
  if (arg == nullptr) return 0;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(arg, &value);
  g_arg_total += static_cast<uint64_t>(value.value.integer);
  return 0;
}

int CountingCompiletf(const char*) {
  ++g_compiletf_runs;
  return 0;
}

// Registers $probe with both routines, so one run answers §36.8.3's count and
// §36.8.2's side by side. A system task rather than a system function because
// §36.5 makes a task the type whose call is a statement, which is the position
// the clause's own example writes its call in.
void RegisterCountingProbe() {
  g_calltf_runs = 0;
  g_compiletf_runs = 0;
  g_arg_total = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &CountingCalltf;
  data.compiletf = &CountingCompiletf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(CalltfApplicationRoutine, RunsOncePerExecutionOfTheOneCallSite) {
  RegisterCountingProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial for (i = 1; i <= 4; i = i + 1) $probe(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // Four executions of the one call the source wrote. The compiletf's count is
  // the discriminating half: a run that called both routines per call site
  // answers 1 here too, and a run that called both per execution answers 4
  // there.
  EXPECT_EQ(g_calltf_runs, 4);
  EXPECT_EQ(g_compiletf_runs, 1);
}

TEST_F(CalltfApplicationRoutine, ReadsTheArgumentsAsTheyStandAtEachExecution) {
  RegisterCountingProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial for (i = 1; i <= 4; i = i + 1) $probe(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // §36.8.3's example has the calltf read a test vector and put it where the
  // design will use it, once per iteration, so each execution is a fresh look
  // at the arguments rather than a repeat of the first. The loop counter is 1,
  // 2, 3 and 4 at the four executions, and 10 is a total only four separate
  // reads produce -- a call object built once and reused adds 1 four times.
  EXPECT_EQ(g_arg_total, 10u);
}

TEST_F(CalltfApplicationRoutine, RunsAgainAtEveryLaterTimeTheCallIsReached) {
  RegisterCountingProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial for (i = 1; i <= 3; i = i + 1) #5 $probe(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // The clause's example reaches its call once per posedge, so the executions
  // it counts are spread through simulation time rather than run off end to end
  // in one step. A delay ahead of the call puts these three at 5, 10 and 15,
  // and the count is the same three.
  EXPECT_EQ(g_calltf_runs, 3);
  EXPECT_EQ(g_arg_total, 6u);
  EXPECT_EQ(g_compiletf_runs, 1);
}

}  // namespace
}  // namespace delta
