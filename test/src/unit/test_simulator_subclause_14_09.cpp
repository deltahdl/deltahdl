#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

TEST(InterfaceClockingSim, TheClauseProgramReachesItsDutThroughModports) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(
                "`timescale 1ns/1ps\n"
                "interface bus_A (input clk);\n"
                "  logic [15:0] data;\n"
                "  logic write;\n"
                "  modport test (input data, output write, input clk);\n"
                "  modport dut (output data, input write, input clk);\n"
                "endinterface\n"
                "interface bus_B (input clk);\n"
                "  logic [8:1] cmd;\n"
                "  logic enable;\n"
                "  modport test (input enable, input clk, inout cmd);\n"
                "  modport dut (output enable, input clk, input cmd);\n"
                "endinterface\n"
                "program test(bus_A.test a, bus_B.test b);\n"
                "  clocking cd1 @(posedge a.clk);\n"
                "    input data = a.data;\n"
                "    output write = a.write;\n"
                "    input state = top.cpu1.state;\n"
                "  endclocking\n"
                "  clocking cd2 @(posedge b.clk);\n"
                "    input #2 output #4ps cmd = b.cmd;\n"
                "    input en = b.enable;\n"
                "  endclocking\n"
                "  initial begin\n"
                "    @(cd1);\n"
                "    $display(\"data=%h state=%0d\", cd1.data, cd1.state);\n"
                "    cd1.write <= 1;\n"
                "    @(cd2);\n"
                "    $display(\"en=%b\", cd2.en);\n"
                "    cd2.cmd <= 8'h3c;\n"
                "    @(cd2); @(cd2);\n"
                "    $display(\"cmd=%h write=%b seen=%h\", cd2.cmd, "
                "top.cpu1.w, top.mem1.got);\n"
                "  end\n"
                "endprogram\n"
                "module cpu(bus_A.dut a);\n"
                "  int state = 7;\n"
                "  logic w;\n"
                "  initial a.data = 16'hbeef;\n"
                "  always @(a.write) w = a.write;\n"
                "endmodule\n"
                "module mem(bus_B.dut b);\n"
                "  logic [8:1] got;\n"
                "  initial b.enable = 1;\n"
                "  always @(b.cmd) got = b.cmd;\n"
                "endmodule\n"
                "module top;\n"
                "  logic phi1 = 0, phi2 = 0;\n"
                "  always #5 phi1 = ~phi1;\n"
                "  initial #2 forever #5 phi2 = ~phi2;\n"
                "  bus_A a (phi1);\n"
                "  bus_B b (phi2);\n"
                "  test main (a, b);\n"
                "  cpu cpu1 (a);\n"
                "  mem mem1 (b);\n"
                "  initial #80 $finish;\n"
                "endmodule\n",
                f),
            "data=beef state=7\nen=1\ncmd=3c write=1 seen=3c\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
