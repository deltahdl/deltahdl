#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr const char* kAndPrimitive =
    "primitive udp_and (y, a, b);\n"
    "  output y;\n"
    "  input a, b;\n"
    "  table\n"
    "  // a b : y\n"
    "    1 1 : 1 ;\n"
    "    0 ? : 0 ;\n"
    "    ? 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kPartialPrimitive =
    "primitive udp_partial (y, a, b);\n"
    "  output y;\n"
    "  input a, b;\n"
    "  table\n"
    "  // a b : y\n"
    "    0 0 : 0 ;\n"
    "    0 1 : 1 ;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kLatchPrimitive =
    "primitive udp_latch (q, ena_, data);\n"
    "  output q; reg q;\n"
    "  input ena_, data;\n"
    "  table\n"
    "  // ena_ data : q : q+\n"
    "    0 1 : ? : 1 ;\n"
    "    0 0 : ? : 0 ;\n"
    "    1 ? : ? : - ;\n"
    "  endtable\n"
    "endprimitive\n";

std::string InstanceDesign(const char* primitive, const char* instantiation,
                           const char* a, const char* b) {
  return std::string(primitive) +
         "module m;\n"
         "  reg a, b;\n"
         "  wire y;\n"
         "  " +
         instantiation + "\n  initial begin a = " + a + "; b = " + b +
         "; end\n"
         "endmodule\n";
}

std::string SettledValue(const std::string& src, const char* name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return "<no-design>";
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr);
  return var == nullptr ? "<no-signal>" : var->value.ToString();
}

TEST(UdpInstanceSim, CombinationalInstanceDrivesOutputTerminalFromTable) {
  EXPECT_EQ(SettledValue(InstanceDesign(kAndPrimitive, "udp_and g (y, a, b);",
                                        "1'b1", "1'b1"),
                         "y"),
            "1");
  EXPECT_EQ(SettledValue(InstanceDesign(kAndPrimitive, "udp_and g (y, a, b);",
                                        "1'b0", "1'b1"),
                         "y"),
            "0");
}

TEST(UdpInstanceSim, UnspecifiedInputCombinationDrivesUnknown) {
  EXPECT_EQ(
      SettledValue(InstanceDesign(kPartialPrimitive, "udp_partial g (y, a, b);",
                                  "1'b0", "1'b1"),
                   "y"),
      "1");
  EXPECT_EQ(
      SettledValue(InstanceDesign(kPartialPrimitive, "udp_partial g (y, a, b);",
                                  "1'b1", "1'b1"),
                   "y"),
      "x");
}

TEST(UdpInstanceSim, DelayOnInstanceHoldsOutputTerminalAtItsOldValue) {
  SimFixture f;
  std::string src = std::string(kAndPrimitive) +
                    "module m;\n"
                    "  reg a, b;\n"
                    "  reg early, late;\n"
                    "  wire y;\n"
                    "  udp_and #5 g (y, a, b);\n"
                    "  initial begin\n"
                    "    a = 1'b0; b = 1'b0;\n"
                    "    #100 b = 1'b1;\n"
                    "    #100 a = 1'b1;\n"
                    "  end\n"
                    "  initial begin #204 early = y; #2 late = y; end\n"
                    "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* early = f.ctx.FindVariable("early");
  auto* late = f.ctx.FindVariable("late");
  ASSERT_NE(early, nullptr);
  ASSERT_NE(late, nullptr);
  EXPECT_EQ(early->value.ToString(), "0");
  EXPECT_EQ(late->value.ToString(), "1");
}

TEST(UdpInstanceSim, DelayOnInstanceIsChargedAtTheTicksWritten) {
  SimFixture f;
  auto* design = ElaborateSrc(
      std::string(kAndPrimitive) +
          "module m;\n"
          "  reg a, b;\n"
          "  wire y;\n"
          "  udp_and #5 g (y, a, b);\n"
          "  initial begin a = 1'b0; b = 1'b0; #10 a = 1'b1; b = 1'b1; end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 15u);
}

TEST(UdpInstanceSim, SequentialInstanceKeepsOneStateForTheRun) {
  EXPECT_EQ(SettledValue(std::string(kLatchPrimitive) +
                             "module m;\n"
                             "  reg ena_, data;\n"
                             "  wire q;\n"
                             "  udp_latch g (q, ena_, data);\n"
                             "  initial begin\n"
                             "    ena_ = 1'b1; data = 1'b0;\n"
                             "    #10 ena_ = 1'b0; data = 1'b1;\n"
                             "    #10 ena_ = 1'b1; data = 1'b0;\n"
                             "  end\n"
                             "endmodule\n",
                         "q"),
            "1");
}

TEST(UdpInstanceSim, InstanceArrayDrivesEachOutputBitFromItsOwnElement) {
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a, b;\n"
                             "  wire [3:0] y;\n"
                             "  udp_and g [3:0] (y, a, b);\n"
                             "  initial begin a = 4'b1100; b = 4'b1010; end\n"
                             "endmodule\n",
                         "y"),
            "1000");
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a;\n"
                             "  reg b;\n"
                             "  wire [3:0] y;\n"
                             "  udp_and g [3:0] (y, a, b);\n"
                             "  initial begin a = 4'b1100; b = 1'b1; end\n"
                             "endmodule\n",
                         "y"),
            "1100");
}

TEST(UdpInstanceSim,
     InstanceArrayReevaluatesOnALaterChangeOfADistributedInput) {
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a, b;\n"
                             "  wire [3:0] y;\n"
                             "  udp_and g [3:0] (y, a, b);\n"
                             "  initial begin\n"
                             "    a = 4'b1100; b = 4'b1010;\n"
                             "    #10 b = 4'b0101;\n"
                             "  end\n"
                             "endmodule\n",
                         "y"),
            "0100");
}

TEST(UdpInstanceSim,
     InstanceArrayWithABroadcastTerminalReevaluatesOnADistributedInput) {
  EXPECT_EQ(SettledValue(std::string(kAndPrimitive) +
                             "module m;\n"
                             "  reg [3:0] a;\n"
                             "  reg enable;\n"
                             "  wire [3:0] z;\n"
                             "  udp_and g [3:0] (z, a, enable);\n"
                             "  initial begin\n"
                             "    a = 4'b1100; enable = 1'b1;\n"
                             "    #10 a = 4'b0011;\n"
                             "  end\n"
                             "endmodule\n",
                         "z"),
            "0011");
}

TEST(UdpInstanceDelayRun, DelayedUdpInsideAChildModuleFollowsItsInputs) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive and2 (y, a, b);\n"
                       "  output y;\n"
                       "  input a, b;\n"
                       "  table\n"
                       "    1 1 : 1 ;\n"
                       "    0 ? : 0 ;\n"
                       "    ? 0 : 0 ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module w (output o, input i1, i2);\n"
                       "  and2 #1 u(o, i1, i2);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg a = 0, b = 1; wire y, yt;\n"
                       "  w i(y, a, b);\n"
                       "  and2 #1 ut(yt, a, b);\n"
                       "  initial begin\n"
                       "    #5 $display(\"%b %b\", y, yt);\n"
                       "    a = 1; #3 $display(\"%b %b\", y, yt);\n"
                       "    b = 0; #3 $display(\"%b %b\", y, yt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 0\n1 1\n0 0\n");
}

TEST(UdpInstanceDelayRun, ParameterDelayedSequentialUdpInsideAStageUpdates) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("primitive dffi (q, clk, d);\n"
                 "  output q; reg q;\n"
                 "  input clk, d;\n"
                 "  initial q = 1'b1;\n"
                 "  table\n"
                 "    (01) 0 : ? : 0 ;\n"
                 "    (01) 1 : ? : 1 ;\n"
                 "    (0?) 1 : 1 : 1 ;\n"
                 "    (0?) 0 : 0 : 0 ;\n"
                 "    (?0) ? : ? : - ;\n"
                 "    ? (?"
                 "?) : ? : - ;\n"
                 "  endtable\n"
                 "endprimitive\n"
                 "module stage #(parameter D = 0) (output q, input clk, d);\n"
                 "  dffi #D u(q, clk, d);\n"
                 "endmodule\n"
                 "module top;\n"
                 "  reg clk = 0, d = 0; wire q1, q2;\n"
                 "  stage #(1) s1(q1, clk, d);\n"
                 "  stage #(0) s2(q2, clk, s1.q);\n"
                 "  initial begin\n"
                 "    #1 $display(\"%b %b\", q1, q2);\n"
                 "    clk = 1; #2 $display(\"%b %b\", q1, s2.q);\n"
                 "    clk = 0; #1 clk = 1; #2 $display(\"%b %b\", q1, q2);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1\n0 1\n0 0\n");
}

TEST(UdpInstanceRun, UnnamedSequentialUdpInsideAChildModuleCaptures) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive posdff_udp(q, clock, data, preset, clear, "
                       "notifier);\n"
                       "  output q; reg q;\n"
                       "  input clock, data, preset, clear, notifier;\n"
                       "  table\n"
                       "    r 0 1 1 ? : ? : 0 ;\n"
                       "    r 1 1 1 ? : ? : 1 ;\n"
                       "    n ? ? ? ? : ? : - ;\n"
                       "    ? * ? ? ? : ? : - ;\n"
                       "    ? ? ? ? * : ? : x ;\n"
                       "  endtable\n"
                       "endprimitive\n"
                       "module dff(q, clock, data);\n"
                       "  output q; input clock, data;\n"
                       "  reg notifier;\n"
                       "  posdff_udp(q, clock, data, 1'b1, 1'b1, notifier);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg clock = 0, data = 0;\n"
                       "  wire q;\n"
                       "  dff u(.q(q), .clock(clock), .data(data));\n"
                       "  initial begin\n"
                       "    #20 data = 1; #20 clock = 1;\n"
                       "    #1 $display(\"%b %b\", u.notifier, q);\n"
                       "    #9 clock = 0; #10 data = 0; #10 clock = 1;\n"
                       "    #1 $display(\"%b %b\", u.notifier, q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "x 1\nx 0\n");
}

TEST(UdpInstanceDelayRun, ALaterChangeSupersedesAPendingOne) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive ubuf (o, a);\n"
                       "  output o; input a;\n"
                       "  table 0 : 0 ; 1 : 1 ; endtable\n"
                       "endprimitive\n"
                       "module top;\n"
                       "  reg a = 0;\n"
                       "  wire q;\n"
                       "  ubuf #(5, 1) u (q, a);\n"
                       "  initial begin\n"
                       "    #10 a = 1;\n"
                       "    #2 a = 0;\n"
                       "    #10 $display(\"%b\", q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n");
}

TEST(UdpInstanceDelayRun, AnEvaluationGivingThePendingValueLeavesItPending) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive ugate (o, a, c);\n"
                       "  output o; input a, c;\n"
                       "  table 0 ? : 0 ; 1 ? : 1 ; endtable\n"
                       "endprimitive\n"
                       "module top;\n"
                       "  reg a = 0, c = 0;\n"
                       "  wire q;\n"
                       "  ugate #5 u (q, a, c);\n"
                       "  initial begin\n"
                       "    #10 a = 1;\n"
                       "    #2 c = 1;\n"
                       "    #4 $display(\"%b\", q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(UdpInstanceSim, ASelectOutputIsADriverOfItsNet) {
  SimFixture f;
  EXPECT_EQ(RunCapture("primitive ubuf (o, a);\n"
                       "  output o; input a;\n"
                       "  table 0 : 0 ; 1 : 1 ; endtable\n"
                       "endprimitive\n"
                       "module top;\n"
                       "  reg a = 0, b = 1;\n"
                       "  wire [1:0] y, y2;\n"
                       "  ubuf (pull0, pull1) g[1:0] (y, {a, a});\n"
                       "  assign y = 2'b11;\n"
                       "  ubuf u (y2[1], b);\n"
                       "  assign y2 = 2'b00;\n"
                       "  initial #1 $display(\"%b %b\", y, y2);\n"
                       "endmodule\n",
                       f),
            "11 x0\n");
}

}  // namespace
