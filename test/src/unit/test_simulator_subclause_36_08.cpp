#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.8 -- VPI sizetf, compiletf, and calltf routines. "VPI-based system tasks
// have sizetf, compiletf, and calltf routines, which perform specific actions
// for the task or system function. The sizetf, compiletf, and calltf routines
// are called during specific periods during processing."
//
// What each of the three does is §36.8.1 through §36.8.4's business and is
// tested in their files. What is left to this one is the sentence those files
// have no case for: that a run has periods, and that the three routines are
// distributed across them rather than all reached from the one moment a call is
// executed. So every case here registers one application carrying all three
// routines and reads the order and the counts a whole run produces.
//
// The order is what discriminates. A tool that ran the sizetf and the compiletf
// from inside the call, which is where the sizetf was reached before, answers
// every count these cases assert and gets the order wrong.

// The routines of the registration under test, in the order the run reached
// them. A calltf is a plain C function, so a file-scope log is where it can
// record that it ran and when relative to the other two.
std::vector<std::string> g_order;

int LoggingSizetf(const char*) {
  g_order.emplace_back("sizetf");
  return 8;
}

int LoggingCompiletf(const char*) {
  g_order.emplace_back("compiletf");
  return 0;
}

int LoggingCalltf(const char*) {
  g_order.emplace_back("calltf");
  return 0;
}

// Registers $probe with all three routines. It is a sized system function so
// that §36.8.1's sizetf is one of the three: the sizetf "shall not be called
// for user-defined system tasks", which would leave a task-typed registration
// with only two periods to show.
void RegisterProbe() {
  g_order.clear();
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = "$probe";
  data.sizetf = &LoggingSizetf;
  data.compiletf = &LoggingCompiletf;
  data.calltf = &LoggingCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// How many entries of `g_order` name `routine`.
int Ran(const std::string& routine) {
  int n = 0;
  for (const auto& entry : g_order) {
    if (entry == routine) ++n;
  }
  return n;
}

class SystfRoutinePeriods : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.8: the three routines are "called during specific periods during
// processing", and this is the whole of that sentence in one run. The design
// calls $probe twice, so the calltf's period -- §36.8.3's "each time the
// associated user-defined system task or system function is executed" -- is
// reached twice, while the two build-period routines run once each and both run
// before the first execution.
//
// The order is asserted as the whole sequence rather than as counts, because
// counts alone are what a tool that reached all three from inside the call
// would also answer.
TEST_F(SystfRoutinePeriods, TheBuildRoutinesRunOnceBeforeAnyExecution) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = $probe();\n"
      "    r = $probe();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_order,
            (std::vector<std::string>{"sizetf", "compiletf", "compiletf",
                                      "calltf", "calltf"}));
}

// §36.8: the periods belong to the design's processing, so a registration the
// design never names reaches none of them. Without this case a build period
// that ran every registration's routines rather than the ones the design uses
// would pass the case above, and §36.8.1's "it shall be called if its
// associated system function appears in the design" is the same reading applied
// to one of the three.
TEST_F(SystfRoutinePeriods, ARegistrationTheDesignNeverNamesReachesNoPeriod) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_TRUE(g_order.empty());
}

// §36.8: the build period covers the design rather than the one procedure the
// call happened to be written in. Here $probe stands in a child module
// instantiated twice and in a function body no process ever calls.
//
// §36.8.2 counts "each instance of a system task or system function in the
// source description", so the compiletf runs twice and not three times: the two
// instances of `c` carry one call between them, elaborated once per instance
// but written once in the source. §36.8.1's sizetf runs once whatever the
// count, being called "at most once" per registration.
//
// The calltf count is what says the two periods are not one walk: it is the two
// instances of `c` and not the function nothing calls, while the compiletf
// reached that function and the calltf never did.
TEST_F(SystfRoutinePeriods, TheBuildPeriodCoversTheWholeDesign) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n"
      "module t;\n"
      "  function automatic int f();\n"
      "    int x;\n"
      "    x = $probe();\n"
      "    return x;\n"
      "  endfunction\n"
      "  c u1();\n"
      "  c u2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(Ran("sizetf"), 1);
  EXPECT_EQ(Ran("compiletf"), 2);
  EXPECT_EQ(Ran("calltf"), 2);
}

// §36.8: a continuous assignment's right-hand side is an expression the source
// description wrote, so the name in it is encountered at build like any other.
// Only the build period is asserted here: how many times §10.3 evaluates an
// assignment whose right-hand side reads nothing is that clause's question,
// while the compiletf's one run is this one's.
TEST_F(SystfRoutinePeriods, ACallInAContinuousAssignmentIsEncountered) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(Ran("sizetf"), 1);
  EXPECT_EQ(Ran("compiletf"), 1);
}

}  // namespace
}  // namespace delta
