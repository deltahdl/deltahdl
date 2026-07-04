// §20.3 Simulation time system functions — head clause. Beyond the Syntax 20-2
// grammar (parser-tested separately), the head states the shared semantic that
// binds the three alternatives: $time, $stime, and $realtime each provide
// access to the *current* simulation time. These tests drive real source —
// with `#` delays advancing the scheduler — through the full pipeline
// (parse → elaborate → lower → run) and observe every one of the three
// functions reporting the simulation time in force where it is evaluated, and
// tracking that time as the scheduler advances. The per-function width and
// scaling rules ($time's rounding, $stime's 32-bit truncation, $realtime's
// fractional real) belong to §20.3.1–§20.3.3 and are covered there; here the
// default 1 ns unit / 1 ns precision leaves the tick count unscaled so each
// function's value equals the elapsed delay, isolating the "current time"
// claim this head owns.
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §20.3: at a nonzero simulation time (reached by a `#5` delay), each of the
// three time functions reports that current time. With the default unscaled
// timescale the reported value is the elapsed tick count, so all three equal 5.
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

// §20.3: the functions read the *current* time, not a fixed snapshot — a second
// read after a further delay reports the later time. $time sees 3 after the
// first delay and 7 after three more ticks elapse.
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

// §20.3: $realtime likewise tracks the advancing current time; read at two
// distinct simulation times it yields the two corresponding real values.
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

// §20.3: $stime, like the other two functions, tracks the advancing current
// time; read at two distinct simulation times within one process it reports
// each time in turn. This exercises the 32-bit function's path across an
// advancing scheduler, mirroring the $time and $realtime cases above.
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

// §20.3: before any delay the current simulation time is zero, and all three
// functions report it as such. This anchors the "current time" claim at the
// start of the run, complementing the nonzero-time cases above.
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
