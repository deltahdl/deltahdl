#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.4 — User-defined system task and system function arguments. A
// user-defined system task or system function written in a source file "can
// have arguments that can be used by the PLI applications associated with the
// system task or system function", the clause's own example being
// `$get_vector("test_vector.pat", input_bus);` with two of them. Those
// arguments are the task/function arguments, and the rule about them is how
// they reach the application: "When the PLI applications associated with a
// user-defined system task or system function are called, the task/function
// arguments are not passed to the PLI application. Instead, a number of PLI
// routines are provided that allow the PLI applications to read and write to
// the task/function arguments."
//
// Both halves are observable from a calltf. The application's own parameter
// carries the user_data its registration gave it and never an argument list,
// and §37.42's vpiArgument iteration over the call handle
// vpi_handle(vpiSysTfCall, NULL) returns is what reaches the arguments.
class SystfCallArguments : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// What the application below found, left at file scope because a calltf is a
// plain C function with nowhere else to put it.
int g_args_seen = 0;
uint64_t g_second_arg = 0;
const char* g_user_data_seen = nullptr;
// The user_data every registration below carries. An array rather than a string
// literal because s_vpi_systf_data::user_data is a void* and the application is
// handed it back unchanged.
char g_user_data[] = "vector-reader";
bool g_user_data_was_read = false;

// Walks the call's arguments the way §36.4 says an application has to: through
// the PLI routines, off the call handle, rather than out of its own parameter.
int ReadArgsCalltf(const char* user_data) {
  g_user_data_seen = user_data;
  g_user_data_was_read = true;
  g_args_seen = 0;
  g_second_arg = 0;
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    ++g_args_seen;
    if (g_args_seen == 2) {
      s_vpi_value value = {};
      value.format = vpiIntVal;
      vpi_get_value(arg, &value);
      g_second_arg = static_cast<uint64_t>(value.value.integer);
    }
  }
  return 0;
}

// Writes through the second argument, which is what §36.4's "write to the
// task/function arguments" names.
int WriteArgCalltf(const char*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  // The first argument is the file name; the second is the variable to write.
  if (vpi_scan(args) == nullptr) return 0;
  vpiHandle arg = vpi_scan(args);
  if (arg == nullptr) return 0;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x2D;
  vpi_put_value(arg, &value, nullptr, vpiNoDelay);
  return 0;
}

// Registers $get_vector under `calltf` and runs the clause's own call site,
// with `input_bus` holding `bus`. Returns the value the variable holds once the
// run is over, so a case that wrote through an argument can read it back.
uint64_t RunGetVector(int (*calltf)(const char*), uint64_t bus, SimFixture& f) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$get_vector";
  task.calltf = calltf;
  task.user_data = g_user_data;
  if (vpi_register_systf(&task) == nullptr) return 0;

  auto* var = RunAndFindVar(
      "module top;\n"
      "  int input_bus;\n"
      "  initial begin\n"
      "    input_bus = " +
          std::to_string(bus) +
          ";\n"
          "    $get_vector(\"test_vector.pat\", input_bus);\n"
          "  end\n"
          "endmodule\n",
      f, "input_bus");
  return var == nullptr ? 0 : var->value.ToUint64();
}

// §36.4: the call site's arguments reach the application. The clause's example
// writes two, so the iteration returns two -- a call object carrying none would
// return zero and read as a task called with no arguments at all.
TEST_F(SystfCallArguments, BothArgumentsOfTheCallSiteAreReachable) {
  g_args_seen = 0;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  EXPECT_EQ(g_args_seen, 2);
}

// §36.4: the routines "allow the PLI applications to read ... the
// task/function arguments". The second argument is `input_bus`, which the
// design set to 8'h5A before the call, so that is what the application reads
// back through vpi_get_value.
TEST_F(SystfCallArguments, AnArgumentsValueIsReadThroughTheRoutines) {
  g_second_arg = 0;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  EXPECT_EQ(g_second_arg, 0x5Au);
}

// §36.4: and to "write to the task/function arguments". The application puts
// 8'h2D through the second argument, so the variable the call site named holds
// it once the run is over rather than the 8'h5A it went in with.
TEST_F(SystfCallArguments, AnArgumentIsWrittenThroughTheRoutines) {
  SimFixture f;
  EXPECT_EQ(RunGetVector(WriteArgCalltf, 0x5A, f), 0x2Du);
}

// §36.4: "the task/function arguments are not passed to the PLI application."
// The one parameter a calltf takes is the user_data its registration carried,
// which is what it is handed here -- not the first argument of the call, and
// not a list of them.
TEST_F(SystfCallArguments, TheApplicationsParameterIsItsOwnUserData) {
  g_user_data_seen = nullptr;
  g_user_data_was_read = false;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  ASSERT_TRUE(g_user_data_was_read);
  EXPECT_STREQ(g_user_data_seen, "vector-reader");
}

}  // namespace
}  // namespace delta
