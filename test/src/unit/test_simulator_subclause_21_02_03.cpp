#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

size_t CountOccurrences(const std::string& haystack,
                        const std::string& needle) {
  size_t count = 0;
  for (size_t pos = haystack.find(needle); pos != std::string::npos;
       pos = haystack.find(needle, pos + needle.size())) {
    ++count;
  }
  return count;
}

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
  EXPECT_EQ(out, "a=0\na=5\na=6\n");
}

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
  EXPECT_EQ(out, "a=5\na=6\n");
}

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
  EXPECT_EQ(CountOccurrences(out, "s="), 2u);
}

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

TEST(IoMonitorSim, MonitorOnResumesMostRecentMonitorAfterSupersede) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'h0; b = 4'h0;\n"
      "    $monitor(\"first=%h\", a);\n"
      "    $monitor(\"second=%h\", b);\n"
      "    #10 b = 4'h4;\n"
      "    #10 $monitoroff;\n"
      "    #10 b = 4'h5;\n"
      "    #10 $monitoron;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "second=0\nsecond=4\nsecond=5\n");
  EXPECT_EQ(out.find("first="), std::string::npos);
}

TEST(IoMonitorSim, MonitorAppliesDisplayStyleCharacterEscape) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial begin\n"
      "    a = 4'ha;\n"
      "    $monitor(\"x\\ty=%h\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\ty=a\n");
}

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

TEST(IoMonitorSim, MonitorInAClassMethodReadsTheMethodsObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class W;\n"
      "    int v = 1;\n"
      "    static int s = 5;\n"
      "    task run;\n"
      "      $monitor(\"%0d %0d %0d\", v, this.v, s);\n"
      "      v = 4;\n"
      "    endtask\n"
      "  endclass\n"
      "  W w = new;\n"
      "  initial w.run();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4 5\n");
}

TEST(IoMonitorSim, MonitorOfAPropertyThroughAHandleFollowsItsWrites) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C; int p = 1; endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    $monitor(\"p=%0d\", h.p);\n"
                       "    #1 h.p = 7;\n"
                       "    #1 $display(\"end\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "p=1\np=7\nend\n");
  SimFixture g;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int p = 1;\n"
                       "    task bump; #2 p = 7; endtask\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    $monitor(\"p=%0d\", h.p);\n"
                       "    h.bump();\n"
                       "    #1 $display(\"end\");\n"
                       "  end\n"
                       "endmodule\n",
                       g),
            "p=1\np=7\nend\n");
}

TEST(IoMonitorSim, MonitorInAMethodFollowsItsObjectAndStaticProperties) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int p = 1, q = 0;\n"
                       "    static int s = 5;\n"
                       "    task run; $monitor(\"%0d %0d %0d\", p, this.p, s);"
                       " endtask\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    h.run();\n"
                       "    #1 h.p = 2;\n"
                       "    #1 h.q = 9;\n"
                       "    #1 C::s = 6;\n"
                       "    #1 $display(\"end\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 5\n2 2 5\n2 2 6\nend\n");
}

}  // namespace
