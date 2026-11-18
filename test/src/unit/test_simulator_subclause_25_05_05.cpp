#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(ClockingModportSim, AProgramDrivesAndSamplesThroughClockingModports) {
  EXPECT_EQ(
      RunWithoutErrors("interface A_Bus(input logic clk);\n"
                       "  wire req, gnt;\n"
                       "  wire [7:0] addr, data;\n"
                       "  clocking sb @(posedge clk);\n"
                       "    input gnt;\n"
                       "    output req, addr;\n"
                       "    inout data;\n"
                       "  endclocking\n"
                       "  modport DUT(input clk, req, addr, output gnt,\n"
                       "              inout data);\n"
                       "  modport STB(clocking sb);\n"
                       "endinterface\n"
                       "module dev(A_Bus.DUT b);\n"
                       "  logic g = 0;\n"
                       "  assign b.gnt = g;\n"
                       "  always @(posedge b.clk) g <= b.req;\n"
                       "endmodule\n"
                       "program T(A_Bus.STB b1, A_Bus.STB b2);\n"
                       "  initial begin\n"
                       "    b1.sb.req <= 1;\n"
                       "    wait (b1.sb.gnt == 1);\n"
                       "    $display(\"b1 %0t\", $time);\n"
                       "    b1.sb.req <= 0;\n"
                       "    b2.sb.req <= 1;\n"
                       "    wait (b2.sb.gnt == 1);\n"
                       "    $display(\"b2 %0t %0d\", $time, top.b1.req);\n"
                       "    b2.sb.req <= 0;\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  A_Bus b1(clk);\n"
                       "  A_Bus b2(clk);\n"
                       "  dev d1(b1);\n"
                       "  dev d2(b2);\n"
                       "  T tb(b1, b2);\n"
                       "endmodule\n"),
      "b1 25\nb2 45 0\n");
}

TEST(ClockingModportSim, ASynchronousAndAnAsynchronousPortOfOneProgram) {
  EXPECT_EQ(RunWithoutErrors("interface A_Bus(input logic clk);\n"
                             "  logic req = 0, gnt = 0;\n"
                             "  clocking sb @(posedge clk);\n"
                             "    input gnt;\n"
                             "    output req;\n"
                             "  endclocking\n"
                             "  modport STB(clocking sb);\n"
                             "  modport TB(input gnt, output req);\n"
                             "endinterface\n"
                             "program T(A_Bus.STB s, A_Bus.TB a);\n"
                             "  initial begin\n"
                             "    s.sb.req <= 1;\n"
                             "    a.req = 1;\n"
                             "    #2 $display(\"%0d %0d\", top.b1.req, "
                             "top.b2.req);\n"
                             "    #10 $display(\"%0d %0d\", top.b1.req, "
                             "top.b2.req);\n"
                             "    @(s.sb);\n"
                             "    $display(\"%0d %0t\", s.sb.gnt, $time);\n"
                             "  end\n"
                             "endprogram\n"
                             "module top;\n"
                             "  logic clk = 0;\n"
                             "  always #5 clk = ~clk;\n"
                             "  A_Bus b1(clk), b2(clk);\n"
                             "  T t(b1, b2);\n"
                             "  initial #13 b1.gnt = 1;\n"
                             "endmodule\n"),
            "0 1\n1 1\n1 15\n");
}

constexpr const char* kBusWithClockedProperties =
    "interface I(input logic clk);\n"
    "  logic req = 0, gnt = 0;\n"
    "  clocking sb @(posedge clk);\n"
    "    property p1; req ##1 gnt; endproperty\n"
    "    sequence s1; req ##1 gnt; endsequence\n"
    "  endclocking\n"
    "  property p0; @(posedge clk) req ##1 gnt; endproperty\n"
    "  property pa(x); @(posedge clk) req ##1 x; endproperty\n"
    "  modport STB(clocking sb);\n"
    "endinterface\n";

std::string Asserted(const std::string& name) {
  return "  int fails = 0;\n"
         "  assert property (" +
         name +
         ") $display(\"pass %0t\", $time);\n"
         "    else fails++;\n"
         "  initial #40 $display(\"fails %0d\", fails);\n";
}

constexpr const char* kStimulus =
    "  logic clk = 0;\n"
    "  initial repeat (6) #5 clk = ~clk;\n"
    "  initial begin\n"
    "    #7 b.req = 1;\n"
    "    #10 b.gnt = 1;\n"
    "    b.req = 0;\n"
    "  end\n";

std::string ThroughAPort(const std::string& header, const std::string& name,
                         const std::string& unit) {
  return std::string(kBusWithClockedProperties) + unit + " u(" + header +
         " b);\n" + Asserted(name) + "end" + unit +
         "\n"
         "module top;\n" +
         kStimulus +
         "  I b(clk);\n"
         "  u inst(b);\n"
         "endmodule\n";
}

TEST(ClockingModportSim,
     AClockingBlockPropertyIsAssertedThroughAProgramModportPort) {
  EXPECT_EQ(RunWithoutErrors(ThroughAPort("I.STB", "b.sb.p1", "program")),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim,
     AClockingBlockPropertyIsAssertedThroughAModuleModportPort) {
  EXPECT_EQ(RunWithoutErrors(ThroughAPort("I.STB", "b.sb.p1", "module")),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AClockingBlockPropertyIsAssertedThroughAPlainPort) {
  EXPECT_EQ(RunWithoutErrors(ThroughAPort("I", "b.sb.p1", "module")),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AnInterfacePropertyIsAssertedThroughAPlainPort) {
  EXPECT_EQ(RunWithoutErrors(ThroughAPort("I", "b.p0", "module")),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AClockingBlockPropertyIsAssertedThroughAnInstance) {
  EXPECT_EQ(RunWithoutErrors(std::string(kBusWithClockedProperties) +
                             "module top;\n" + kStimulus + "  I b(clk);\n" +
                             Asserted("b.sb.p1") + "endmodule\n"),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AClockingBlockSequenceIsAssertedThroughAModportPort) {
  EXPECT_EQ(RunWithoutErrors(ThroughAPort("I.STB", "b.sb.s1", "module")),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AnInterfacePropertyWithAnArgumentThroughAPort) {
  EXPECT_EQ(RunWithoutErrors(ThroughAPort("I", "b.pa(b.gnt)", "module")),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AnInterfacePropertyIsAssertedThroughAnInstance) {
  EXPECT_EQ(RunWithoutErrors(std::string(kBusWithClockedProperties) +
                             "module top;\n" + kStimulus + "  I b(clk);\n" +
                             Asserted("b.p0") + "endmodule\n"),
            "pass 25\nfails 2\n");
}

TEST(ClockingModportSim, AClockingBlockPropertyIsAssertedInItsOwnScope) {
  EXPECT_EQ(RunWithoutErrors("module top;\n"
                             "  logic clk = 0, req = 0, gnt = 0;\n"
                             "  initial repeat (6) #5 clk = ~clk;\n"
                             "  clocking sb @(posedge clk);\n"
                             "    property p1; req ##1 gnt; endproperty\n"
                             "  endclocking\n"
                             "  initial begin\n"
                             "    #7 req = 1;\n"
                             "    #10 gnt = 1;\n"
                             "    req = 0;\n"
                             "  end\n" +
                             Asserted("sb.p1") + "endmodule\n"),
            "pass 25\nfails 2\n");
}

}  // namespace
