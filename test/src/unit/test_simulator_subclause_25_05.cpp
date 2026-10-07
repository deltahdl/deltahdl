#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.5 (printed page 787): a connection may name a modport of the interface
// instance, named hierarchically from that instance, and the port then reaches
// that instance's own members. A program reading the modport's input through a
// `Bus.tb` port sees the value the module placed on `s.q`. The program's
// initial waits past the module's read at 3, since its end would end the run
// (§24.3).
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

// The same connection into a module: the read of the modport's input and the
// write of its output both land on the one instance `s`.
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

// §25.5's own example on printed page 787: plain `i2 i` ports connected as
// `.i(i.initiator)` and `.i(i.target)` share the one instance `i`, so what
// each module writes the other reads.
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

// §25.5.5 and §25.9.1 (printed pages 791-792 and 803) with §14: a clocking
// block is a member of the interface declaring it, sampled and driven at its
// event through every name denoting the instance -- the instance's own path,
// `b1.sb.req <= 1`; a class property of the clocking modport's virtual
// interface type, `@(vif.sb)` and `vif.sb.a`; and a formal of that type,
// `wait (s.sb.gnt == 1)`. The drive through the path was dropped, the read
// through the virtual interface gave 0, and the wait never woke.
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

}  // namespace
