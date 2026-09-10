#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.8.2: a compiletf application is typically used to check the correctness
// of the arguments a user-defined system task or function is given. These stubs
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
// user-defined system task or system function name is encountered during
// parsing or compiling the SystemVerilog source code." and "shall be called one
// time for each instance ... in the source description." The when of that call
// is delegated to §36.10.2 and §38.37.1; what §36.8.2 itself fixes is that
// compiletf runs while the design is being compiled/built - in contrast to
// calltf, which runs on every invocation during simulation. That
// compile-time-per-instance classification is what distinguishes compiletf from
// the execution-time routine.
// -----------------------------------------------------------------------------

TEST_F(CompiletfApplicationRoutine, IsACompileTimeRoutineUnlikeCalltf) {
  // compiletf fires while the simulation data structure is compiled/built...
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCompiletf));
  // ...whereas calltf fires per execution during simulation, not at compile
  // time.
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

// -----------------------------------------------------------------------------
// §36.8.2: the routine is called when "the user-defined system task or system
// function name is encountered". Unlike sizetf (functions only, §36.8.1),
// compiletf applies to both kinds, so the same compiletf application runs
// whether the registration is a system task or a system function.
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
  // The single argument passed is the registration's user_data, typed as char
  // *.
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));

  ResetCompiletfProbe();
  VpiSystfInvoke(func.compiletf, func.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));
}

// -----------------------------------------------------------------------------
// §36.8.2: "Providing a compiletf routine is optional." A registration that
// supplies no compiletf application is accepted and reads back with no
// compiletf, and asking the runtime to run the absent routine is a harmless
// no-op.
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

TEST_F(CompiletfApplicationRoutine,
       SuppliedRoutineRoundTripsAndReceivesUserData) {
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
// §36.8.2: "This routine is typically used to check the correctness of any
// arguments passed to the user-defined system task or system function in the
// SystemVerilog source code." §36.4 leaves an application no way to those
// arguments other than the call handle vpi_handle(vpiSysTfCall, NULL) answers
// with -- "the task/function arguments are not passed to the PLI application"
// and §38.37.1 makes user_data "the only argument passed to the compiletf,
// sizetf, and calltf routines" -- so a compiletf run with no call standing is a
// compiletf that can check nothing at all. The cases below run a real design
// and let the application look.
// -----------------------------------------------------------------------------

// What the compiletf below found, left at file scope because a compiletf is a
// plain C function with no return path to the case that provoked it. The two
// names are copied rather than kept as pointers: §38.11 has vpi_get_str() place
// its answer in one buffer reused by every call, so the pointer from the first
// call names the second call's string by the time a case reads it.
int g_call_type_seen = 0;
int g_args_seen_at_compile = -1;
std::string g_call_name_seen;
std::string g_first_arg_name_seen;

int InspectingCompiletf(const char*) {
  g_call_type_seen = 0;
  g_args_seen_at_compile = -1;
  g_call_name_seen.clear();
  g_first_arg_name_seen.clear();

  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  g_call_type_seen = vpi_get(vpiType, call);
  const char* call_name = vpi_get_str(vpiName, call);
  if (call_name != nullptr) g_call_name_seen = call_name;

  vpiHandle args = vpi_iterate(vpiArgument, call);
  g_args_seen_at_compile = 0;
  if (args == nullptr) return 0;
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    ++g_args_seen_at_compile;
    if (g_args_seen_at_compile != 1) continue;
    const char* arg_name = vpi_get_str(vpiName, arg);
    if (arg_name != nullptr) g_first_arg_name_seen = arg_name;
  }
  return 0;
}

// Registers $probe with the inspecting compiletf and no calltf. The calltf is
// left out because §36.8.2's period is the build rather than the execution, and
// a registration with nothing to run at execution is what keeps the two apart:
// everything a case below reads was written before the scheduler ran an event.
void RegisterInspectingProbe(int type) {
  s_vpi_systf_data data = {};
  data.type = type;
  data.tfname = "$probe";
  data.compiletf = &InspectingCompiletf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(CompiletfApplicationRoutine, ReachesTheCallTheSourceWroteItFor) {
  RegisterInspectingProbe(vpiSysTask);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial $probe(r, 1 + 2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // The call the compiletf was run for is the one the source wrote: a system
  // task call named by the registration's tfname, carrying the two arguments
  // the call site listed. A compiletf reached with no call standing leaves
  // every one of these at the value it was cleared to.
  EXPECT_EQ(g_call_type_seen, vpiSysTaskCall);
  EXPECT_EQ(g_call_name_seen, "$probe");
  EXPECT_EQ(g_args_seen_at_compile, 2);
  // §36.4: an argument that names a variable is reached as that variable, which
  // is what lets a compiletf say which name a call was written against.
  EXPECT_EQ(g_first_arg_name_seen, "r");
}

TEST_F(CompiletfApplicationRoutine, ReachesASystemFunctionCallTheSameWay) {
  // §36.8.2 applies to both kinds -- the routine is called "when the
  // user-defined system task or system function name is encountered" -- and
  // §37.42 gives a function call its own object type, so the application can
  // tell which kind it is checking the arguments of.
  RegisterInspectingProbe(vpiSysFunc);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe(r);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_call_type_seen, vpiSysFuncCall);
  EXPECT_EQ(g_call_name_seen, "$probe");
  EXPECT_EQ(g_args_seen_at_compile, 1);
  EXPECT_EQ(g_first_arg_name_seen, "r");
}

}  // namespace
}  // namespace delta
