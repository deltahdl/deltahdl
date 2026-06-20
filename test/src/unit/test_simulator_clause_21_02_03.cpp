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

size_t CountOccurrences(const std::string& haystack,
                        const std::string& needle) {
  size_t count = 0;
  for (size_t pos = haystack.find(needle); pos != std::string::npos;
       pos = haystack.find(needle, pos + needle.size())) {
    ++count;
  }
  return count;
}

// §21.2.3: $monitor redisplays the whole argument list each time a watched
// value changes; the first display establishes the initial values. The flag is
// on by default, so no $monitoron is needed for output to appear.
TEST(IoMonitorSim, RedisplaysOnValueChange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h0;\n"
      "    $monitor(\"a=%h\", a);\n"
      "    #10 a = 4'h1;\n"
      "    #10 a = 4'h2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=0\na=1\na=2\n");
}

// §21.2.3: when two or more arguments change at the same simulation time, only
// one display is produced showing all the new values.
TEST(IoMonitorSim, SimultaneousChangesProduceOneDisplay) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'h0; b = 4'h0;\n"
      "    $monitor(\"a=%h b=%h\", a, b);\n"
      "    #10 begin a = 4'h1; b = 4'h1; end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=0 b=0\na=1 b=1\n");
}

// §21.2.3: a change in $time, $stime, or $realtime does not trigger the
// monitor. Time advances over two delays here, but with the watched value held
// constant only the single initial display appears.
TEST(IoMonitorSim, TimeFunctionChangeDoesNotTrigger) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    $monitor(\"%0t a=%h\", $time, a);\n"
      "    #10;\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountOccurrences(out, "a=5"), 1u);
}

// §21.2.3: $stime is explicitly excluded alongside $time from the set of
// expressions whose advance triggers a $monitor redisplay. Time advances over
// two delays but only the initial line is produced.
TEST(IoMonitorSim, StimeChangeDoesNotTrigger) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    $monitor(\"%0d a=%h\", $stime, a);\n"
      "    #10;\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountOccurrences(out, "a=5"), 1u);
}

// §21.2.3: $realtime is the third explicitly excluded time function. Even with
// the value of $realtime changing across delays, only the single initial
// display is produced for a constant watched value.
TEST(IoMonitorSim, RealtimeChangeDoesNotTrigger) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    $monitor(\"%0t a=%h\", $realtime, a);\n"
      "    #10;\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountOccurrences(out, "a=5"), 1u);
}

// §21.2.3: only one monitor display list is active at a time. A second
// $monitor supersedes the first, whose signals then no longer redisplay.
TEST(IoMonitorSim, SecondMonitorSupersedesFirst) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'h0; b = 4'h0;\n"
      "    $monitor(\"first=%h\", a);\n"
      "    #10 $monitor(\"second=%h\", b);\n"
      "    #10 a = 4'h7;\n"
      "    #10 b = 4'h9;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountOccurrences(out, "first="), 1u);
  EXPECT_EQ(out.find("first=7"), std::string::npos);
  EXPECT_NE(out.find("second=0"), std::string::npos);
  EXPECT_NE(out.find("second=9"), std::string::npos);
}

// §21.2.3: $monitoroff disables monitoring and $monitoron re-enables it. A
// value change while the flag is off produces no display, but $monitoron
// produces a display immediately upon being invoked.
TEST(IoMonitorSim, MonitorOffSuppressesAndMonitorOnResumes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h0;\n"
      "    $monitor(\"a=%h\", a);\n"
      "    #10 $monitoroff;\n"
      "    #10 a = 4'h5;\n"
      "    #10 $monitoron;\n"
      "    #10 a = 4'h6;\n"
      "  end\n"
      "endmodule\n",
      f);
  // The a=5 change while off is silent; $monitoron then displays it once, and
  // the later a=6 change displays again.
  EXPECT_EQ(out, "a=0\na=5\na=6\n");
}

// §21.2.3: $monitoron produces a display the moment it is invoked even when no
// watched value has changed since the previous display. Here nothing changes
// between the initial display and the $monitoroff/$monitoron pair, yet the
// second line still appears.
TEST(IoMonitorSim, MonitorOnDisplaysWithoutAnyValueChange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h3;\n"
      "    $monitor(\"a=%h\", a);\n"
      "    #10 $monitoroff;\n"
      "    #10 $monitoron;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=3\na=3\n");
}

// §21.2.3 (Syntax 21-3): $monitorh is one of the four monitor task names and is
// treated as a monitor that redisplays on a value change.
TEST(IoMonitorSim, MonitorhIsRecognizedAsMonitor) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h0a;\n"
      "    $monitorh(\"a=%h\", a);\n"
      "    #10 a = 8'h0b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=0a\na=0b\n");
}

// §21.2.3 (Syntax 21-3): $monitorb likewise sets up monitoring.
TEST(IoMonitorSim, MonitorbIsRecognizedAsMonitor) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h0a;\n"
      "    $monitorb(\"a=%h\", a);\n"
      "    #10 a = 8'h0b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=0a\na=0b\n");
}

// §21.2.3 (Syntax 21-3): $monitoro likewise sets up monitoring.
TEST(IoMonitorSim, MonitoroIsRecognizedAsMonitor) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h0a;\n"
      "    $monitoro(\"a=%h\", a);\n"
      "    #10 a = 8'h0b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=0a\na=0b\n");
}

// §21.2.3: the monitor reacts to a value *change*. Writing a watched variable
// its current value is not a change, so no redisplay is produced for it.
TEST(IoMonitorSim, SameValueWriteDoesNotRedisplay) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    $monitor(\"a=%h\", a);\n"
      "    #10 a = 4'h5;\n"
      "    #10 a = 4'h6;\n"
      "  end\n"
      "endmodule\n",
      f);
  // The mid write of the same value is silent; only the initial display and
  // the genuine change to 6 appear.
  EXPECT_EQ(out, "a=5\na=6\n");
}

// §21.2.3: the monitor watches expressions, not just plain variables. A change
// to any operand of a monitored expression triggers a redisplay.
TEST(IoMonitorSim, MonitorsExpressionArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'h1; b = 4'h2;\n"
      "    $monitor(\"s=%h\", a + b);\n"
      "    #10 a = 4'h4;\n"
      "  end\n"
      "endmodule\n",
      f);
  // One initial display plus one redisplay caused by the change to operand a.
  EXPECT_EQ(CountOccurrences(out, "s="), 2u);
}

// §21.2.3: $monitor arguments are handled exactly as $display arguments,
// including format escapes such as %% for a literal percent sign.
TEST(IoMonitorSim, MonitorAppliesDisplayStyleFormatEscape) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    $monitor(\"a=%h%%\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=5%\n");
}

// §21.2.3: $monitoron resumes the most recent $monitor. With no monitor ever
// established it has nothing to display and must remain silent.
TEST(IoMonitorSim, MonitorOnWithNoActiveMonitorIsSilent) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $monitoron;\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "");
}

}  // namespace
