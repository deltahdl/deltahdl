#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kSimpleBus =
    "interface simple_bus(input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  logic [1:0] mode;\n"
    "  logic start = 0, rdy;\n"
    "  task initiatorRead(input logic [7:0] raddr);\n"
    "    addr = raddr;\n"
    "    start = ~start;\n"
    "    $display(\"%m %h at %0t\", raddr, $time);\n"
    "  endtask: initiatorRead\n"
    "  task targetRead;\n"
    "    data = addr + 1;\n"
    "    $display(\"%m %h at %0t\", data, $time);\n"
    "  endtask: targetRead\n"
    "endinterface: simple_bus\n";

std::string RunOnTheBus(const std::string& modules) {
  SimFixture f;
  std::string out = RunCapture(std::string(kSimpleBus) + modules, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(InterfaceTaskSim, TwoModulesShareOneInstanceThroughGenericPorts) {
  EXPECT_EQ(RunOnTheBus("module memMod(interface a);\n"
                        "  logic avail = 1;\n"
                        "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
                        "  always @(a.start) a.targetRead;\n"
                        "endmodule\n"
                        "module cpuMod(interface b);\n"
                        "  enum {read, write} instr = read;\n"
                        "  logic [7:0] raddr = 8'h5a;\n"
                        "  always @(posedge b.clk)\n"
                        "    if (instr == read) b.initiatorRead(raddr);\n"
                        "endmodule\n"
                        "module top;\n"
                        "  logic clk = 0;\n"
                        "  simple_bus sb_intf(clk);\n"
                        "  memMod mem(sb_intf);\n"
                        "  cpuMod cpu(sb_intf);\n"
                        "  initial begin\n"
                        "    sb_intf.req = 1;\n"
                        "    #5 clk = 1;\n"
                        "    #1 $display(\"gnt %b data %h\", sb_intf.gnt, "
                        "sb_intf.data);\n"
                        "  end\n"
                        "endmodule\n"),
            "top.sb_intf.initiatorRead 5a at 5\n"
            "top.sb_intf.targetRead 5b at 5\n"
            "gnt 1 data 5b\n");
}

TEST(InterfaceTaskSim, ATaskWithoutArgumentsIsCalledWithoutParentheses) {
  EXPECT_EQ(RunOnTheBus("module m(interface a);\n"
                        "  initial begin\n"
                        "    a.addr = 8'h10;\n"
                        "    #1 a.targetRead;\n"
                        "    #1 a.targetRead();\n"
                        "  end\n"
                        "endmodule\n"
                        "module top;\n"
                        "  logic clk = 0;\n"
                        "  simple_bus sb_intf(clk);\n"
                        "  m u(sb_intf);\n"
                        "endmodule\n"),
            "top.sb_intf.targetRead 11 at 1\n"
            "top.sb_intf.targetRead 11 at 2\n");
}

TEST(InterfaceTaskSim,
     ACallThroughThePortWritesTheInterfaceTheOtherModuleReads) {
  EXPECT_EQ(RunOnTheBus("module writer(interface b);\n"
                        "  initial #1 b.initiatorRead(8'h33);\n"
                        "endmodule\n"
                        "module reader(interface a);\n"
                        "  initial #2 $display(\"addr %h start %b\", a.addr, "
                        "a.start);\n"
                        "endmodule\n"
                        "module top;\n"
                        "  logic clk = 0;\n"
                        "  simple_bus sb_intf(clk);\n"
                        "  writer w(sb_intf);\n"
                        "  reader r(sb_intf);\n"
                        "endmodule\n"),
            "top.sb_intf.initiatorRead 33 at 1\naddr 33 start 1\n");
}

TEST(InterfaceTaskSim, AnInterfacePortSignalClocksTheConnectedModule) {
  EXPECT_EQ(RunOnTheBus("module memMod(interface a);\n"
                        "  always @(posedge a.clk) a.gnt <= a.req;\n"
                        "endmodule\n"
                        "module top;\n"
                        "  logic clk = 0;\n"
                        "  simple_bus sb_intf(clk);\n"
                        "  memMod mem(sb_intf);\n"
                        "  initial begin\n"
                        "    sb_intf.req = 1; sb_intf.gnt = 0;\n"
                        "    #1 $display(\"before %b\", sb_intf.gnt);\n"
                        "    clk = 1;\n"
                        "    #1 $display(\"after %b\", sb_intf.gnt);\n"
                        "  end\n"
                        "endmodule\n"),
            "before 0\nafter 1\n");
}

}  // namespace
