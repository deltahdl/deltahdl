#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ModportConnectionSim, ProgramReadsModportInputThroughSelectedConnection) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface Bus;\n"
                       "  int q, d;\n"
                       "  modport tb(input q, output d);\n"
                       "endinterface\n"
                       "program P(Bus.tb b);\n"
                       "  initial begin\n"
                       "    #2 $display(\"prog q=%0d at %0t\", b.q, $time);\n"
                       "    b.d = 1;\n"
                       "    #2;\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  Bus s();\n"
                       "  initial s.q = 61;\n"
                       "  initial #3 $display(\"top d=%0d\", s.d);\n"
                       "  P pi(s.tb);\n"
                       "endmodule\n",
                       f),
            "prog q=61 at 2\ntop d=1\n");
}

TEST(ModportConnectionSim, ModuleReadsAndWritesThroughSelectedConnection) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface Bus;\n"
                       "  int q, d;\n"
                       "  modport tb(input q, output d);\n"
                       "endinterface\n"
                       "module sub(Bus.tb b);\n"
                       "  initial begin\n"
                       "    #2 $display(\"sub q=%0d at %0t\", b.q, $time);\n"
                       "    b.d = 1;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  Bus s();\n"
                       "  initial s.q = 61;\n"
                       "  initial #3 $display(\"top d=%0d\", s.d);\n"
                       "  sub si(s.tb);\n"
                       "endmodule\n",
                       f),
            "sub q=61 at 2\ntop d=1\n");
}

TEST(ModportConnectionSim, TwoModportsOfOneInstanceShareItsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i2;\n"
                       "  int x, y;\n"
                       "  modport initiator(input x, output y);\n"
                       "  modport target(output x, input y);\n"
                       "endinterface\n"
                       "module m(i2 i);\n"
                       "  initial begin #1 i.y = 5; #1 $display(\"m x=%0d\", "
                       "i.x); end\n"
                       "endmodule\n"
                       "module s(i2 i);\n"
                       "  initial begin i.x = 9; #3 $display(\"s y=%0d\", "
                       "i.y); end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  i2 i();\n"
                       "  m u1(.i(i.initiator));\n"
                       "  s u2(.i(i.target));\n"
                       "  initial #4 $display(\"top x=%0d y=%0d\", i.x, i.y);\n"
                       "endmodule\n",
                       f),
            "m x=9\ns y=5\ntop x=9 y=5\n");
}

TEST(ModportConnectionSim,
     InterfaceClockingBlockThroughEveryNameOfTheInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "interface A_Bus(input logic clk);\n"
      "  logic req, gnt, a;\n"
      "  clocking sb @(posedge clk);\n"
      "    input gnt, a;\n"
      "    output req;\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n"
      "typedef virtual A_Bus.STB SYNCTB;\n"
      "class Tb;\n"
      "  virtual A_Bus.STB vif;\n"
      "  function new(virtual A_Bus.STB v); vif = v; endfunction\n"
      "  task run(); @(vif.sb); $write(\"%0t:%0d \", $time, vif.sb.a); "
      "endtask\n"
      "endclass\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  A_Bus b1(clk);\n"
      "  always @(posedge clk) b1.gnt <= b1.req;\n"
      "  task automatic wait_grant(SYNCTB s); wait (s.sb.gnt == 1); endtask\n"
      "  initial begin\n"
      "    automatic Tb tb = new(b1);\n"
      "    b1.req = 0; b1.gnt = 0; b1.a = 1;\n"
      "    b1.sb.req <= 1;\n"
      "    tb.run();\n"
      "    wait_grant(b1);\n"
      "    $display(\"%0t %0d\", $time, b1.req);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5:1 25 1\n$finish at time 25\n");
}

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(ModportConnectionSim, ARefItemIsReadAndWrittenThroughTheModportPort) {
  EXPECT_EQ(RunWithoutErrors("interface bus;\n"
                             "  int r;\n"
                             "  modport mp(ref r);\n"
                             "endinterface\n"
                             "module child(bus.mp b);\n"
                             "  initial begin\n"
                             "    b.r = 5;\n"
                             "    #1 $display(\"child %0d\", b.r);\n"
                             "    b.r = b.r + 1;\n"
                             "  end\n"
                             "endmodule\n"
                             "module top;\n"
                             "  bus i();\n"
                             "  child c(i);\n"
                             "  initial #2 $display(\"top %0d\", i.r);\n"
                             "endmodule\n"),
            "child 5\ntop 6\n");
}

TEST(ModportlessPortSim, DISABLED_AStructMemberReadsThroughThePort) {
  EXPECT_EQ(
      RunWithoutErrors("interface bus(input logic clk, a);\n"
                       "  typedef struct packed { logic f; logic g; } ps_t;\n"
                       "  ps_t s;\n"
                       "  struct { logic f; } us;\n"
                       "  always_comb begin s.f = a; s.g = ~a; us.f = a; end\n"
                       "endinterface\n"
                       "module m(bus ip, input logic clk);\n"
                       "  initial #2 $display(\"%b %b %b\", ip.s.f, ip.s.g, "
                       "ip.us.f);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0, a = 0;\n"
                       "  bus ub(clk, a);\n"
                       "  m u(ub, clk);\n"
                       "  initial #1 a = 1;\n"
                       "endmodule\n"),
      "1 0 1\n");
}

std::string RunSharedInstance(const std::string& instances) {
  return RunWithoutErrors(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a, input logic clk);\n"
      "  logic avail = 1;\n"
      "  always @(posedge clk) a.gnt <= a.req & avail;\n"
      "endmodule\n"
      "module cpuMod(simple_bus b, input logic clk);\n"
      "  wire seen = b.gnt;\n"
      "  initial begin\n"
      "    b.req = 1;\n"
      "    #12 b.req = 0;\n"
      "    #10 b.req = 1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0, old;\n"
      "  initial repeat (6) #5 clk = ~clk;\n"
      "  simple_bus sb_intf();\n" +
      instances +
      "  always @(posedge clk) begin\n"
      "    old = sb_intf.gnt;\n"
      "    $strobe(\"%0t %b->%b %b %b\", $time, old, sb_intf.gnt, "
      "sb_intf.req, cpu.seen);\n"
      "  end\n"
      "endmodule\n");
}

TEST(ModportlessPortSim, TwoModulesShareOneInstanceThroughNamedConnections) {
  EXPECT_EQ(RunSharedInstance("  memMod mem(.a(sb_intf), .clk(clk));\n"
                              "  cpuMod cpu(.b(sb_intf), .clk(clk));\n"),
            "5 x->1 1 1\n15 1->0 0 0\n25 0->1 1 1\n");
}

TEST(ModportlessPortSim,
     TwoModulesShareOneInstanceThroughPositionalConnections) {
  EXPECT_EQ(RunSharedInstance("  memMod mem(sb_intf, clk);\n"
                              "  cpuMod cpu(sb_intf, clk);\n"),
            "5 x->1 1 1\n15 1->0 0 0\n25 0->1 1 1\n");
}

TEST(ModportlessPortSim, APortSelectingNoModportWritesEveryMember) {
  EXPECT_EQ(
      RunWithoutErrors("interface bus;\n"
                       "  logic a, z;\n"
                       "  wire w;\n"
                       "  modport mp(input a);\n"
                       "endinterface\n"
                       "module m(bus b);\n"
                       "  assign b.w = 1;\n"
                       "  initial begin\n"
                       "    b.a = 1;\n"
                       "    b.z = 1;\n"
                       "    #1 $display(\"in %b %b %b\", b.a, b.z, b.w);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus i();\n"
                       "  m u(.b(i));\n"
                       "  initial #2 $display(\"a=%b z=%b w=%b\", i.a, i.z, "
                       "i.w);\n"
                       "endmodule\n"),
      "in 1 1 1\na=1 z=1 w=1\n");
}

}  // namespace
