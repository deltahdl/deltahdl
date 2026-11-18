#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InterfaceExportSim, ExportedTaskRunsInTheDefiningModule) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus;\n"
                       "  logic [7:0] addr;\n"
                       "  modport target(ref addr, export Read);\n"
                       "  modport initiator(ref addr, import task "
                       "Read(input logic [7:0] raddr));\n"
                       "endinterface\n"
                       "module memMod(simple_bus.target a);\n"
                       "  logic avail = 1;\n"
                       "  task a.Read(input logic [7:0] raddr);\n"
                       "    avail = 0;\n"
                       "    #4 $display(\"Read raddr=%0d avail=%0d\", raddr, "
                       "avail);\n"
                       "    avail = 1;\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module cpuMod(simple_bus.initiator b);\n"
                       "  initial begin\n"
                       "    b.Read(17);\n"
                       "    $display(\"after avail=%0d t=%0t\", "
                       "top.mem.avail, $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  simple_bus sb_intf();\n"
                       "  memMod mem(sb_intf.target);\n"
                       "  cpuMod cpu(sb_intf.initiator);\n"
                       "endmodule\n",
                       f),
            "Read raddr=17 avail=0\nafter avail=1 t=4\n");
}

TEST(InterfaceExportSim, AnInitiatorAlternatesTheTwoTasksATargetExports) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface simple_bus(input logic clk);\n"
          "  logic req, gnt;\n"
          "  logic [7:0] addr, data;\n"
          "  logic [1:0] mode;\n"
          "  logic start, rdy;\n"
          "  modport target(input req, addr, mode, start, clk,\n"
          "    output gnt, rdy, ref data, export Read, Write);\n"
          "  modport initiator(input gnt, rdy, clk,\n"
          "    output req, addr, mode, start, ref data,\n"
          "    import task Read(input logic [7:0] raddr),\n"
          "           task Write(input logic [7:0] waddr));\n"
          "endinterface: simple_bus\n"
          "module memMod(interface a);\n"
          "  logic avail = 1;\n"
          "  task a.Read(input logic [7:0] raddr);\n"
          "    avail = 0;\n"
          "    $display(\"%m %h avail %b at %0t\", raddr, avail, $time);\n"
          "    avail = 1;\n"
          "  endtask\n"
          "  task a.Write(input logic [7:0] waddr);\n"
          "    avail = 0;\n"
          "    a.data = waddr;\n"
          "    $display(\"%m %h at %0t\", a.data, $time);\n"
          "    avail = 1;\n"
          "  endtask\n"
          "endmodule\n"
          "module cpuMod(interface b);\n"
          "  enum {read, write} instr = read;\n"
          "  logic [7:0] raddr = 8'h21;\n"
          "  always @(posedge b.clk) begin\n"
          "    if (instr == read) b.Read(raddr);\n"
          "    else b.Write(raddr);\n"
          "    instr = instr.next;\n"
          "    raddr = raddr + 1;\n"
          "  end\n"
          "endmodule\n"
          "module top;\n"
          "  logic clk = 0;\n"
          "  simple_bus sb_intf(clk);\n"
          "  memMod mem(sb_intf.target);\n"
          "  cpuMod cpu(sb_intf.initiator);\n"
          "  initial begin\n"
          "    #5 clk = 1; #5 clk = 0; #5 clk = 1;\n"
          "    #1 $display(\"data %h avail %b\", sb_intf.data, mem.avail);\n"
          "  end\n"
          "endmodule\n",
          f),
      "top.mem.Read 21 avail 0 at 5\ntop.mem.Write 22 at 15\n"
      "data 22 avail 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InterfaceExportSim, AnExportedFunctionIsAnOperandOfTheImporter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface sb;\n"
                       "  modport target(export Peek);\n"
                       "  modport initiator(import function logic [7:0] "
                       "Peek(input logic [7:0] off));\n"
                       "endinterface\n"
                       "module memMod(interface a);\n"
                       "  logic [7:0] base = 8'h10;\n"
                       "  function logic [7:0] a.Peek(input logic [7:0] off);\n"
                       "    return base + off;\n"
                       "  endfunction\n"
                       "endmodule\n"
                       "module cpuMod(interface b);\n"
                       "  initial #1 $display(\"%h\", b.Peek(8'h3) + 8'h1);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sb s();\n"
                       "  memMod mem(s.target);\n"
                       "  cpuMod cpu(s.initiator);\n"
                       "endmodule\n",
                       f),
            "14\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
