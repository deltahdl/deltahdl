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
    "  modport target(input req, addr, mode, start, clk, output gnt, rdy, ref "
    "data, import targetRead, targetWrite);\n"
    "  modport initiator(input gnt, rdy, clk, output req, addr, mode, start, "
    "ref data, import initiatorRead, initiatorWrite);\n"
    "  task initiatorRead(input logic [7:0] raddr); addr = raddr; mode = 0; "
    "start = ~start; $display(\"%m %h at %0t\", raddr, $time); endtask\n"
    "  task targetRead; data = addr + 1; $display(\"%m %h at %0t\", data, "
    "$time); endtask\n"
    "  task initiatorWrite(input logic [7:0] waddr); addr = waddr; mode = 1; "
    "start = ~start; $display(\"%m %h at %0t\", waddr, $time); endtask\n"
    "  task targetWrite; data = addr - 1; $display(\"%m %h at %0t\", data, "
    "$time); endtask\n"
    "endinterface: simple_bus\n";

TEST(ModportTaskSim, EachModuleCallsTheTasksOfItsModportAndOmniCallsAll) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kSimpleBus) +
                     "module memMod(interface a);\n"
                     "  logic avail = 1;\n"
                     "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
                     "  always @(a.start) if (a.mode[0] == 1'b0) a.targetRead; "
                     "else a.targetWrite;\n"
                     "endmodule\n"
                     "module cpuMod(interface b);\n"
                     "  enum {read, write} instr = read;\n"
                     "  logic [7:0] raddr = 8'h40;\n"
                     "  always @(posedge b.clk) begin\n"
                     "    if (instr == read) b.initiatorRead(raddr); else "
                     "b.initiatorWrite(raddr);\n"
                     "    instr = instr.next;\n"
                     "  end\n"
                     "endmodule\n"
                     "module omniMod(interface b);\n"
                     "  initial begin #20 b.initiatorRead(1); #1 b.targetRead; "
                     "b.initiatorWrite(2); #1 b.targetWrite; end\n"
                     "endmodule: omniMod\n"
                     "module top;\n"
                     "  logic clk = 0;\n"
                     "  simple_bus sb_intf(clk);\n"
                     "  memMod mem(sb_intf.target);\n"
                     "  cpuMod cpu(sb_intf.initiator);\n"
                     "  omniMod omni(sb_intf);\n"
                     "  initial begin sb_intf.req = 1; #5 clk = 1; #5 clk = 0; "
                     "#5 clk = 1; #1 $display(\"gnt %b\", sb_intf.gnt); end\n"
                     "endmodule\n",
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out,
            "top.sb_intf.initiatorRead 40 at 5\n"
            "top.sb_intf.targetRead 41 at 5\n"
            "top.sb_intf.initiatorWrite 40 at 15\n"
            "top.sb_intf.targetWrite 3f at 15\n"
            "gnt 1\n"
            "top.sb_intf.initiatorRead 01 at 20\n"
            "top.sb_intf.targetRead 02 at 20\n"
            "top.sb_intf.targetRead 02 at 21\n"
            "top.sb_intf.initiatorWrite 02 at 21\n"
            "top.sb_intf.targetWrite 01 at 21\n"
            "top.sb_intf.targetWrite 01 at 22\n");
}

}  // namespace
