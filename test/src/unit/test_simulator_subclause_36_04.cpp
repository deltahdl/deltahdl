#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §36.4 — User-defined system task and system function arguments. A
// user-defined system task or system function written in a source file may take
// arguments that the PLI applications tied to it can use, the clause's own
// example being `$get_vector("test_vector.pat", input_bus);` with two of them.
// Those arguments are the task/function arguments, and the rule about them is
// how they reach the application: a called PLI application is not handed them,
// and reads and writes them instead through PLI routines provided for the
// purpose.
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
PLI_INT32 ReadArgsCalltf(PLI_BYTE8* user_data) {
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

// Writes through the second argument, the write to a task/function argument
// that §36.4 names.
PLI_INT32 WriteArgCalltf(PLI_BYTE8*) {
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
uint64_t RunGetVector(PLI_INT32 (*calltf)(PLI_BYTE8*), uint64_t bus,
                      SimFixture& f) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$get_vector");
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

// §36.4: the routines let the PLI applications read the task/function
// arguments. The second argument is `input_bus`, which the design set to 8'h5A
// before the call, so that is what the application reads back through
// vpi_get_value.
TEST_F(SystfCallArguments, AnArgumentsValueIsReadThroughTheRoutines) {
  g_second_arg = 0;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  EXPECT_EQ(g_second_arg, 0x5Au);
}

// §36.4: and let them write to the task/function arguments. The application
// puts 8'h2D through the second argument, so the variable the call site named
// holds it once the run is over rather than the 8'h5A it went in with.
TEST_F(SystfCallArguments, AnArgumentIsWrittenThroughTheRoutines) {
  SimFixture f;
  EXPECT_EQ(RunGetVector(WriteArgCalltf, 0x5A, f), 0x2Du);
}

// §36.4: the PLI application is not handed the task/function arguments. The one
// parameter a calltf takes is the user_data its registration carried, which is
// what it is handed here -- not the first argument of the call, and not a list
// of them.
TEST_F(SystfCallArguments, TheApplicationsParameterIsItsOwnUserData) {
  g_user_data_seen = nullptr;
  g_user_data_was_read = false;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  ASSERT_TRUE(g_user_data_was_read);
  EXPECT_STREQ(g_user_data_seen, "vector-reader");
}

// What $kinds found of each argument: its type, its constant type or operator,
// and its value.
struct ArgumentSeen {
  int type;
  int kind;
  int value;
};
std::vector<ArgumentSeen>& KindsSeen() {
  static std::vector<ArgumentSeen> seen;
  return seen;
}

PLI_INT32 KindsCalltf(PLI_BYTE8*) {
  vpiHandle args = vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    const int kType = vpi_get(vpiType, arg);
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(arg, &value);
    KindsSeen().push_back({kType,
                           kType == vpiConstant ? vpi_get(vpiConstType, arg)
                                                : vpi_get(vpiOpType, arg),
                           value.value.integer});
  }
  return 0;
}

// §36.4 with §37.42 and §37.58: each argument the call site wrote reaches the
// application as what it is -- an unbased unsized literal an integer constant,
// a real literal a real constant, an omitted argument an operation of the null
// operator (§37.42 detail 8) -- and a member of a structure, through a name or
// through an element of an array, as an expression holding the member's value.
TEST_F(SystfCallArguments, EachArgumentKindReachesTheApplication) {
  KindsSeen().clear();
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$kinds");
  task.calltf = KindsCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  RunAndFindVar(
      "module top;\n"
      "  typedef struct packed {logic [7:0] f;} s_t;\n"
      "  s_t s = 8'h21; s_t sa [2];\n"
      "  initial begin sa[0] = 8'h43; $kinds('1, 2.5, , s.f, sa[0].f); end\n"
      "endmodule\n",
      f, "s");
  ASSERT_EQ(KindsSeen().size(), 5u);
  EXPECT_EQ(KindsSeen()[0].type, vpiConstant);
  EXPECT_EQ(KindsSeen()[0].kind, vpiIntConst);
  EXPECT_EQ(KindsSeen()[1].type, vpiConstant);
  EXPECT_EQ(KindsSeen()[1].kind, vpiRealConst);
  EXPECT_EQ(KindsSeen()[2].type, vpiOperation);
  EXPECT_EQ(KindsSeen()[2].kind, vpiNullOp);
  EXPECT_EQ(KindsSeen()[3].value, 0x21);
  EXPECT_EQ(KindsSeen()[4].value, 0x43);
}

PLI_INT32 ZeroSizetf(PLI_BYTE8*) { return 0; }

PLI_INT32 AllOnesCalltf(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = -1;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

// §36.8.1 with §38.37.1: a sizetf answering with no bits describes no value,
// so a sized system function returns the default 32 bits: all ones written
// through the call reads back as 32 ones, zero-extended into a 64-bit
// variable.
TEST_F(SystfCallArguments, ASizetfOfNoBitsLeavesTheDefaultWidth) {
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiSizedFunc;
  func.tfname = VpiText("$zero_wide");
  func.calltf = AllOnesCalltf;
  func.sizetf = ZeroSizetf;
  ASSERT_NE(vpi_register_systf(&func), nullptr);
  SimFixture f;
  auto* r = RunAndFindVar(
      "module top; logic [63:0] r; initial r = $zero_wide(); endmodule\n", f,
      "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0xFFFFFFFFu);
}

int g_elsewhere_calls = 0;

PLI_INT32 CountCalltf(PLI_BYTE8*) {
  if (vpi_handle(vpiSysTfCall, nullptr) != nullptr) ++g_elsewhere_calls;
  return 0;
}

// §36.4 with §37.42 detail 3: a call written in a package function and one
// written in a task of an instance reached by a hierarchical call each reach
// the application with a call object, whichever instance the call runs from.
TEST_F(SystfCallArguments, ACallWrittenOutsideTheRunningInstanceIsReached) {
  g_elsewhere_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$elsewhere");
  task.calltf = CountCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  RunAndFindVar(
      "package p;\n"
      "  function automatic int f(); $elsewhere; return 1; endfunction\n"
      "endpackage\n"
      "module sub; task t(); $elsewhere; endtask endmodule\n"
      "module top; int x; sub u();\n"
      "  initial begin x = p::f(); u.t(); end\n"
      "endmodule\n",
      f, "x");
  EXPECT_EQ(g_elsewhere_calls, 2);
}

}  // namespace
}  // namespace delta
