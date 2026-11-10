#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InterfaceBuildingBlockSim, ModuleDrivesTheBundleThroughItsPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus(input logic clk);\n"
                       "  logic req, gnt;\n"
                       "endinterface : simple_bus\n"
                       "module memMod(simple_bus a);\n"
                       "  logic avail = 1;\n"
                       "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  simple_bus sb_intf(.clk(clk));\n"
                       "  memMod mem(.a(sb_intf));\n"
                       "  initial begin\n"
                       "    sb_intf.req = 1;\n"
                       "    sb_intf.gnt = 0;\n"
                       "    #1 clk = 1;\n"
                       "    #1 $display(\"gnt=%0d\", sb_intf.gnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "gnt=1\n");
}

TEST(InterfaceBuildingBlockSim, TwoModulesShareOneInstanceThroughTheirPorts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface link;\n"
                       "  logic [7:0] data;\n"
                       "endinterface\n"
                       "module sender(link s);\n"
                       "  initial s.data = 8'd42;\n"
                       "endmodule\n"
                       "module receiver(link r);\n"
                       "  initial #1 $display(\"data=%0d\", r.data);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  link l();\n"
                       "  sender tx(.s(l));\n"
                       "  receiver rx(.r(l));\n"
                       "endmodule\n",
                       f),
            "data=42\n");
}

TEST(InterfaceBuildingBlockSim, ProgramReachesTheBundleThroughItsPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface link;\n"
                       "  logic [7:0] data;\n"
                       "endinterface\n"
                       "program bench(link p);\n"
                       "  initial begin\n"
                       "    p.data = p.data + 8'd1;\n"
                       "    $display(\"port=%0d instance=%0d\", p.data, "
                       "top.l.data);\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  link l();\n"
                       "  bench b(.p(l));\n"
                       "  initial l.data = 8'd16;\n"
                       "endmodule\n",
                       f),
            "port=17 instance=17\n");
}

TEST(InterfaceBuildingBlockSim, InterfaceReachesTheBundleThroughItsPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface link;\n"
                       "  logic [7:0] data;\n"
                       "endinterface\n"
                       "interface wrapper(link inner);\n"
                       "  initial inner.data = 8'd9;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  link l();\n"
                       "  wrapper w(.inner(l));\n"
                       "  initial #1 $display(\"data=%0d\", l.data);\n"
                       "endmodule\n",
                       f),
            "data=9\n");
}

TEST(InterfaceBuildingBlockSim, MembersAreReachedThroughTheInstanceName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface regs #(parameter int W = 4);\n"
                 "  localparam int DOUBLE = 2 * W;\n"
                 "  logic [W-1:0] value;\n"
                 "  function int width();\n"
                 "    return W;\n"
                 "  endfunction\n"
                 "  task store(input int x);\n"
                 "    value = x;\n"
                 "  endtask\n"
                 "endinterface\n"
                 "module top;\n"
                 "  regs #(.W(6)) r();\n"
                 "  initial begin\n"
                 "    r.store(37);\n"
                 "    $display(\"v=%0d w=%0d d=%0d\", r.value, r.width(), "
                 "r.DOUBLE);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "v=37 w=6 d=12\n");
}

TEST(InterfaceBuildingBlockSim, ModuleCallsTheSubroutinesOfItsInterface) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface counter;\n"
                       "  int count = 0;\n"
                       "  task bump(input int by);\n"
                       "    count = count + by;\n"
                       "  endtask\n"
                       "  function int read();\n"
                       "    return count;\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "module user(counter c);\n"
                       "  initial begin\n"
                       "    c.bump(3);\n"
                       "    c.bump(4);\n"
                       "    $display(\"count=%0d\", c.read());\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  counter cnt();\n"
                       "  user u(.c(cnt));\n"
                       "endmodule\n",
                       f),
            "count=7\n");
}

TEST(InterfaceBuildingBlockSim, ElementTypeIsPassedAsAParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface holder #(parameter type T = int);\n"
                       "  T item;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  holder #(.T(logic [2:0])) narrow();\n"
                       "  holder wide();\n"
                       "  initial $display(\"%0d %0d\", $bits(narrow.item), "
                       "$bits(wide.item));\n"
                       "endmodule\n",
                       f),
            "3 32\n");
}

TEST(InterfaceBuildingBlockSim, ElementTypeIsDeclaredInsideTheInterface) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface framed;\n"
                       "  typedef struct packed {\n"
                       "    logic [3:0] tag;\n"
                       "    logic [7:0] body;\n"
                       "  } frame_t;\n"
                       "  frame_t frame;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  framed fr();\n"
                       "  initial begin\n"
                       "    fr.frame.tag = 4'hA;\n"
                       "    fr.frame.body = 8'h3C;\n"
                       "    $display(\"%0d %h\", $bits(fr.frame), fr.frame);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "12 a3c\n");
}

TEST(InterfaceBuildingBlockSim, ModportGivesDirectionsSeenFromTheModule) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface pipe;\n"
                       "  logic [7:0] in_val, out_val;\n"
                       "  modport stage(input in_val, output out_val);\n"
                       "endinterface\n"
                       "module adder(pipe.stage p);\n"
                       "  assign p.out_val = p.in_val + 8'd1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  pipe link();\n"
                       "  adder a(.p(link));\n"
                       "  initial begin\n"
                       "    link.in_val = 8'd5;\n"
                       "    #1 $display(\"out=%0d\", link.out_val);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "out=6\n");
}

TEST(InterfaceBuildingBlockSim, InterfaceHoldsProcessesAndContinuousAssigns) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface watcher;\n"
                       "  logic a = 0;\n"
                       "  logic inverted;\n"
                       "  int changes = 0;\n"
                       "  assign inverted = ~a;\n"
                       "  always @(a) changes = changes + 1;\n"
                       "  initial begin\n"
                       "    #1 a = 1;\n"
                       "    #1 a = 0;\n"
                       "  end\n"
                       "endinterface\n"
                       "module top;\n"
                       "  watcher w();\n"
                       "  initial #3 $display(\"inv=%0d changes=%0d\", "
                       "w.inverted, w.changes);\n"
                       "endmodule\n",
                       f),
            "inv=1 changes=2\n");
}

TEST(InterfaceBuildingBlockSim, InterfaceHoldsAProtocolCheck) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface handshake;\n"
                 "  logic req = 0, gnt = 0;\n"
                 "  always @(gnt) if (gnt && !req) $display(\"violation\");\n"
                 "endinterface\n"
                 "module top;\n"
                 "  handshake h();\n"
                 "  initial begin\n"
                 "    #1 h.req = 1;\n"
                 "    #1 h.gnt = 1;\n"
                 "    #1 h.req = 0;\n"
                 "    h.gnt = 0;\n"
                 "    #1 h.gnt = 1;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "violation\n");
}

}  // namespace
