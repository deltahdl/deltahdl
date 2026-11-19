#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

TEST(MixedPathDistributedDelay, ModulePathLargerWins) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 1), 22u);
}

TEST(MixedPathDistributedDelay, DistributedSumLargerWins) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 30), 30u);
}

TEST(MixedPathDistributedDelay, EqualDelaysYieldThatValue) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 22), 22u);
}

TEST(MixedPathDistributedDelay, NoDistributedDelayUsesModulePath) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 0), 22u);
}

TEST(MixedPathDistributedDelay, NoModulePathUsesDistributedDelay) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 30), 30u);
}

std::string CellWithGatesAndAModulePath(const std::string& or_delay) {
  return "module mycell(input a, input b, input c, input d, output q);\n"
         "  wire w1, w2;\n"
         "  and #0 (w1, a, b);\n"
         "  and #0 (w2, c, d);\n"
         "  or #" +
         or_delay +
         " (q, w1, w2);\n"
         "  specify\n"
         "    (d *> q) = 22;\n"
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic a, b, c, d;\n"
         "  wire tq;\n"
         "  mycell u(.a(a), .b(b), .c(c), .d(d), .q(tq));\n"
         "  always @(tq) if ($time > 0) $display(\"t=%0t q=%b\", $time, tq);\n"
         "  initial begin\n"
         "    a = 0; b = 0; c = 1; d = 0;\n"
         "    #40 d = 1;\n"
         "    #40 d = 0;\n"
         "  end\n"
         "endmodule\n";
}

TEST(MixedPathDistributedDelayRun, ModulePathLargerWinsOverGates) {
  SimFixture f;
  EXPECT_EQ(RunCapture(CellWithGatesAndAModulePath("1"), f),
            "t=22 q=0\nt=62 q=1\nt=102 q=0\n");
}

TEST(MixedPathDistributedDelayRun, GatesLargerWinOverModulePath) {
  SimFixture f;
  EXPECT_EQ(RunCapture(CellWithGatesAndAModulePath("30"), f),
            "t=30 q=0\nt=70 q=1\nt=110 q=0\n");
}

TEST(MixedPathDistributedDelayRun, AssignmentDelayLargerWinsOverModulePath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybuf(input a, output y);\n"
                       "  assign #10 y = a;\n"
                       "  specify\n"
                       "    (a => y) = 4;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a; wire ty;\n"
                       "  mybuf u(.a(a), .y(ty));\n"
                       "  always @(ty) if ($time >= 12) $display(\"t=%0t "
                       "y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 0;\n"
                       "    #10 a = 1;\n"
                       "    #10 a = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=20 y=1\nt=30 y=0\n");
}

std::string MixedDelayRun(const std::string& before, const std::string& body,
                          const std::string& paths) {
  SimFixture f;
  std::string specify;
  if (!paths.empty()) specify = "  specify\n" + paths + "  endspecify\n";
  return RunCapture(before + "module mycell(input a, input d, output q);\n" +
                        body + specify +
                        "endmodule\n"
                        "module top;\n"
                        "  logic a, d;\n"
                        "  wire tq;\n"
                        "  mycell u(.a(a), .d(d), .q(tq));\n"
                        "  always @(tq) if ($time >= 100)\n"
                        "    $write(\"%0d%b \", $time, tq);\n"
                        "  initial begin\n"
                        "    a = 0; d = 0;\n"
                        "    #100 d = 1;\n"
                        "    #100 d = 0;\n"
                        "    #100 a = 1;\n"
                        "    #100 a = 0;\n"
                        "  end\n"
                        "endmodule\n",
                    f);
}

TEST(MixedPathDistributedDelayRun, GateSumInSeriesWinsOverModulePath) {
  EXPECT_EQ(MixedDelayRun("",
                          "  wire w;\n"
                          "  buf #10 (w, d);\n"
                          "  buf #20 (q, w);\n",
                          "    (d => q) = 22;\n"),
            "1301 2300 ");
}

TEST(MixedPathDistributedDelayRun, EqualGateSumAndModulePathGiveThatDelay) {
  EXPECT_EQ(MixedDelayRun("",
                          "  wire w;\n"
                          "  buf #10 (w, d);\n"
                          "  buf #12 (q, w);\n",
                          "    (d => q) = 22;\n"),
            "1221 2220 ");
}

TEST(MixedPathDistributedDelayRun, EachTransitionTakesItsOwnLargerDelay) {
  EXPECT_EQ(MixedDelayRun("", "  buf #(1, 30) (q, d);\n",
                          "    (d => q) = (22, 5);\n"),
            "1221 2300 ");
}

TEST(MixedPathDistributedDelayRun, ModulePathAloneIsUsedUnchanged) {
  EXPECT_EQ(MixedDelayRun("", "  buf (q, d);\n", "    (d => q) = 22;\n"),
            "1221 2220 ");
}

TEST(MixedPathDistributedDelayRun, GateDelayAloneIsUsedUnchanged) {
  EXPECT_EQ(MixedDelayRun("", "  buf #30 (q, d);\n", ""), "1301 2300 ");
}

TEST(MixedPathDistributedDelayRun, EachPathComparesWithItsOwnGateSum) {
  EXPECT_EQ(MixedDelayRun("",
                          "  wire w;\n"
                          "  buf #30 (w, a);\n"
                          "  or #1 (q, w, d);\n",
                          "    (a => q) = 22;\n"
                          "    (d => q) = 22;\n"),
            "1221 2220 3311 4310 ");
}

TEST(MixedPathDistributedDelayRun, UdpInstanceDelayWinsOverModulePath) {
  EXPECT_EQ(MixedDelayRun("primitive ubuf(output o, input i);\n"
                          "  table\n"
                          "    0 : 0;\n"
                          "    1 : 1;\n"
                          "  endtable\n"
                          "endprimitive\n",
                          "  ubuf #30 (q, d);\n", "    (d => q) = 22;\n"),
            "1301 2300 ");
}

TEST(MixedPathDistributedDelayRun, InvertingGateSumWinsOverModulePath) {
  EXPECT_EQ(MixedDelayRun("",
                          "  wire w;\n"
                          "  not #20 (w, d);\n"
                          "  not #10 (q, w);\n",
                          "    (d => q) = 22;\n"),
            "1301 2300 ");
}

TEST(MixedPathDistributedDelayRun, ChildInstanceGateDelayWinsOverModulePath) {
  EXPECT_EQ(MixedDelayRun("module leaf(input i, output o);\n"
                          "  buf #30 (o, i);\n"
                          "endmodule\n",
                          "  leaf l(.i(d), .o(q));\n", "    (d => q) = 22;\n"),
            "1301 2300 ");
}

}  // namespace
