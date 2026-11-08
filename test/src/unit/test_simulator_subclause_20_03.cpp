#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(TimeFunctionSim, AllThreeReportCurrentTime) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #5;\n"
      "    if ($time == 5) $display(\"time_ok\");\n"
      "    if ($stime == 5) $display(\"stime_ok\");\n"
      "    if ($realtime == 5.0) $display(\"realtime_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "time_ok\nstime_ok\nrealtime_ok\n");
}

TEST(TimeFunctionSim, TimeTracksAdvancingScheduler) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #3;\n"
      "    if ($time == 3) $display(\"t3\");\n"
      "    #4;\n"
      "    if ($time == 7) $display(\"t7\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t3\nt7\n");
}

TEST(TimeFunctionSim, RealtimeTracksAdvancingScheduler) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #2;\n"
      "    if ($realtime == 2.0) $display(\"r2\");\n"
      "    #6;\n"
      "    if ($realtime == 8.0) $display(\"r8\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "r2\nr8\n");
}

TEST(TimeFunctionSim, StimeTracksAdvancingScheduler) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #4;\n"
      "    if ($stime == 4) $display(\"s4\");\n"
      "    #5;\n"
      "    if ($stime == 9) $display(\"s9\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s4\ns9\n");
}

TEST(TimeFunctionSim, AllThreeReportZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    if ($time == 0) $display(\"time0\");\n"
      "    if ($stime == 0) $display(\"stime0\");\n"
      "    if ($realtime == 0.0) $display(\"realtime0\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "time0\nstime0\nrealtime0\n");
}

}  // namespace
