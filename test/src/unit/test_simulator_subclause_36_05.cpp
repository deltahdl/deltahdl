#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.5 — User-defined system task and system function types. The clause's
// first sentence is the whole of it: "The type of a user-defined system task or
// system function determines how a PLI application is called from the
// SystemVerilog source code." What the two types then differ in is the position
// the call may stand in. A task "can be used in the same places a SystemVerilog
// void function can be used (see 13.4)", and §13.4.1 has one such place --
// "function calls may be used as expressions unless of type void, which are
// statements" -- while a function "can be used in the same places a
// SystemVerilog function can be used" and "returns a value".
//
// So every case here registers one application twice, under the two types, and
// holds the design source still. The type is the only thing that moves, which
// is what the clause says decides the outcome.
//
// The other two halves of the clause are stated elsewhere and are not restated
// here: that both types "can read and modify the arguments" is §36.4's file,
// and that a function's vector width comes from the sizetf is §36.8.1's.
class SystfTypes : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// How many times the application below has run. The calltf is a plain C
// function, so a file-scope counter is where it can record that it was reached
// at all -- which is the difference between a call that was refused and one
// that was made.
int g_dual_calls = 0;

int DualCalltf(const char*) {
  ++g_dual_calls;
  return 0;
}

// Registers DualCalltf as `$dual` under `type` and runs the source given.
void RunDual(int type, const std::string& src, SimFixture& f) {
  s_vpi_systf_data data = {};
  data.type = type;
  // §38.37.1 has the sysfunctype read only when the type is vpiSysFunc, so
  // one registration serves both runs and the type stays the only difference
  // between them.
  data.sysfunctype = vpiSizedFunc;
  data.tfname = "$dual";
  data.calltf = DualCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

// The source both position cases use. `$dual` stands on the right of an
// assignment, which is the one place §13.4.1 keeps a void function out of.
constexpr const char* kDualAsAnOperand =
    "module t;\n"
    "  int r;\n"
    "  initial r = $dual();\n"
    "endmodule\n";

// §36.5 with the type set to vpiSysTask: the call site wants a value and a task
// has none to give, so the application is not reached and the use is reported.
// Both halves are asserted because a dispatch that reported the use and ran the
// application anyway would leave the run with a side effect the clause does not
// allow it, and one that ran it silently would fail only the report.
TEST_F(SystfTypes, ATaskTypedRegistrationIsRefusedWhereAValueIsWanted) {
  g_dual_calls = 0;
  SimFixture f;
  RunDual(vpiSysTask, kDualAsAnOperand, f);

  EXPECT_EQ(g_dual_calls, 0);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dual is a user-defined system task and returns "
                            "no value, so it cannot be used as an expression",
                            3, "36.5"));
}

// The same application, the same source, the type alone changed: a function
// "can be used in the same places a SystemVerilog function can be used", so the
// operand position is one of its own and the application is reached. Without
// this case a dispatch that refused every registered name in an expression
// would pass the case above.
TEST_F(SystfTypes, AFunctionTypedRegistrationIsCalledWhereAValueIsWanted) {
  g_dual_calls = 0;
  SimFixture f;
  RunDual(vpiSysFunc, kDualAsAnOperand, f);

  EXPECT_EQ(g_dual_calls, 1);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The position a task does have. §36.3.1's file already has a registered task
// reached from a design; what is asserted here is the other side of the case
// above -- that refusing the operand position did not refuse the task
// altogether, which is the way a rule of this shape is usually got wrong.
TEST_F(SystfTypes, ATaskTypedRegistrationIsCalledWhereAStatementStands) {
  g_dual_calls = 0;
  SimFixture f;
  RunDual(vpiSysTask,
          "module t;\n"
          "  initial $dual;\n"
          "endmodule\n",
          f);

  EXPECT_EQ(g_dual_calls, 1);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The severity vpi_chk_error() reported after the put below, recorded from
// inside the calltf because that is the only place the call handle exists.
int g_put_error_level = 0;

// §37.42 gives the application the call it is running under, and writing a
// value through that handle is how a system function delivers its result. This
// application does it from a task.
int PutThroughTheCallCalltf(const char*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 42;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  g_put_error_level = vpi_chk_error(nullptr);
  return 0;
}

// §36.5: a task "does not return any value", so the call it is running under
// has no return value for a write to land in, and §38.34's list of what
// vpi_put_value() "can be applied to" names system function calls with no
// system task call beside them. The write is refused and the error is
// recorded, which vpi_chk_error() reports to the application that made it.
//
// The function form of the same write is asserted in §36.8.1's file, where a
// design reads back the value a calltf put through its call: a put refused
// there would take that case with it, so nothing here needs to repeat it.
TEST_F(SystfTypes, ATaskCallRefusesAValuePutThroughIt) {
  g_put_error_level = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$put_from_task";
  data.calltf = PutThroughTheCallCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $put_from_task;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_put_error_level, vpiError);
}

}  // namespace
}  // namespace delta
