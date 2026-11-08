#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PrinttimescaleSysTask, NoArgumentDescribesCurrentScope) {
  SimFixture f;
  std::string out = RunCapture(
      "module a_dat;\n"
      "  timeunit 1ms / 1us;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (a_dat) is 1ms / 1us\n");
}

TEST(PrinttimescaleSysTask, NamedElementArgumentDescribesThatElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  child c1();\n"
      "  initial $printtimescale(c1);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (c1) is 100ps / 10fs\n");
}

TEST(PrinttimescaleSysTask, UnitArgumentDescribesCompilationUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "timeunit 1s / 1ms;\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  initial $printtimescale($unit);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of ($unit) is 1s / 1ms\n");
}

TEST(PrinttimescaleSysTask, RootArgumentDescribesSimulationTimeUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  timeunit 1ns / 1fs;\n"
      "  initial $printtimescale($root);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of ($root) is 1fs / 1fs\n");
}

TEST(PrinttimescaleSysTask, ReportFollowsRequiredFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module dut;\n"
      "  timeunit 100us / 10ns;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (dut) is 100us / 10ns\n");
}

TEST(PrinttimescaleSysTask, RendersWholeSecondUnits) {
  SimFixture f;
  std::string out = RunCapture(
      "module slow;\n"
      "  timeunit 100s / 10s;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (slow) is 100s / 10s\n");
}

TEST(PrinttimescaleSysTask, DefaultCurrentScopeIsNanosecond) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (top) is 1ns / 1ns\n");
}

}  // namespace
