#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.6 -- User-supplied PLI applications. "User-supplied PLI applications are
// C language functions that utilize the library of PLI C functions to access
// and interact dynamically with SystemVerilog software implementations as the
// SystemVerilog source code is executed."
//
// What the applications here do is what the clause says one is: each is a plain
// C function that reaches the running design through the library and through
// nothing else. It is handed no design, no context and no arguments -- §36.8.4
// gives a calltf its registered user_data and that is all -- so vpi_*() is the
// only way it has of finding out what the design holds, which is what makes
// these cases about the clause rather than about the routines they are carried
// by.
//
// The design a case runs is the discriminating half. Every value the
// application reads is one the design assigned while it ran, and never the
// declared value, so a tool answering from the source text rather than from the
// live storage gives a different answer.

// What the application made of the design, recorded where a test can read it
// once the run is over. A calltf is a C function with no return path to the
// case, so file scope is the only place it has to leave this.
int g_seen = 0;

// The application: it reaches the design's `r` by name and reads what the
// design has just put there. Neither call is guarded, because both routines
// answer a null handle by leaving the value alone -- so a run that put the
// design nowhere leaves `g_seen` at what it was rather than crashing, and the
// case reports the difference as a value.
int ReadRCalltf(const char*) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name("r", nullptr), &val);
  g_seen = val.value.integer;
  return 0;
}

// The other direction of "interact dynamically": the application writes into
// the design's `r`, and the design reads the write back afterwards.
int WriteRCalltf(const char*) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 42;
  vpi_put_value(vpi_handle_by_name("r", nullptr), &val, nullptr, vpiNoDelay);
  return 0;
}

// Registers `calltf` as $probe. The registration is a system task rather than a
// system function because §36.5 makes a task the type that "can read and modify
// the arguments of the task, but does not return any value", and a value the
// call site would take is not what any case here is about.
void RegisterProbe(int (*calltf)(const char*)) {
  g_seen = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = calltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class PliApplicationDesignAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.6: the application accesses the implementation "as the SystemVerilog
// source code is executed", so what it reads is the value the design holds at
// the moment it runs. `r` is declared without an initializer and assigned 7 by
// the statement before the call, so 7 is a value only the live storage carries.
TEST_F(PliApplicationDesignAccess, TheApplicationReadsTheDesignAsItRuns) {
  RegisterProbe(&ReadRCalltf);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = 7;\n"
      "    $probe;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_seen, 7);
}

// §36.6: "interact dynamically" is both directions, so a value the application
// writes through the library is a value the design goes on to read. The design
// copies `r` into `after` once the call has returned, and 42 arriving there is
// the write having landed in the storage the design reads rather than in a copy
// of it.
TEST_F(PliApplicationDesignAccess, TheApplicationWritesWhereTheDesignReads) {
  RegisterProbe(&WriteRCalltf);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  int after;\n"
      "  initial begin\n"
      "    r = 1;\n"
      "    $probe;\n"
      "    after = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* after = f.ctx.FindVariable("after");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->value.ToUint64(), 42u);
}

// §36.6: the applications the clause describes are the ones "linked into a tool
// and become part of the tool", and a run holding none of them has nothing to
// reach the design through this library. §36.9 gives an application two ways of
// becoming part of the tool and this run has taken neither, so the design is
// left where it was and the name resolves to nothing.
TEST_F(PliApplicationDesignAccess, ARunWithNoApplicationAttachesNothing) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(vpi_handle_by_name("r", nullptr), nullptr);
}

}  // namespace
}  // namespace delta
