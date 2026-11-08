#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<std::string> g_order;

PLI_INT32 LoggingSizetf(PLI_BYTE8*) {
  g_order.emplace_back("sizetf");
  return 8;
}

PLI_INT32 LoggingCompiletf(PLI_BYTE8*) {
  g_order.emplace_back("compiletf");
  return 0;
}

PLI_INT32 LoggingCalltf(PLI_BYTE8*) {
  g_order.emplace_back("calltf");
  return 0;
}

void RegisterProbe() {
  g_order.clear();
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = VpiText("$probe");
  data.sizetf = &LoggingSizetf;
  data.compiletf = &LoggingCompiletf;
  data.calltf = &LoggingCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

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
