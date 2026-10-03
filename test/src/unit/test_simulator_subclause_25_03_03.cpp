#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.3.3: a generic interface port names whatever instance is connected to
// it, so memMod's `a.data = '1` fills sb's 16-bit data, and cpuMod reads sb's
// addr and its localparam True through `interface.mp b` connected as sb.mp.
// Before the port took its interface from the connected instance, the write
// was lost and both reads gave 0 or x: `sum=1 true=0`, `data=x`.
TEST(GenericInterfacePortSim, ReachesTheConnectedInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus #(DWIDTH = 8);\n"
                       "  logic [7:0] addr;\n"
                       "  logic [DWIDTH-1:0] data;\n"
                       "  localparam True = 1;\n"
                       "  modport mp(input addr);\n"
                       "endinterface\n"
                       "module memMod(interface a);\n"
                       "  initial a.data = '1;\n"
                       "endmodule\n"
                       "module cpuMod(interface.mp b);\n"
                       "  initial #1 $display(\"sum=%0d true=%0d\", b.addr + "
                       "1, b.True);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  simple_bus #(.DWIDTH(16)) sb();\n"
                       "  initial sb.addr = 5;\n"
                       "  memMod mem(.a(sb));\n"
                       "  cpuMod cpu(.b(sb.mp));\n"
                       "  initial #2 $display(\"data=%0d\", sb.data);\n"
                       "endmodule\n",
                       f),
            "sum=6 true=1\ndata=65535\n");
}

// §25.3.3 with §16.14: a concurrent assertion in a module reads the
// connected instance's signals through a generic port, `m.req |=> m.gnt`
// clocked on `m.clk`, and runs its action blocks: of the attempts before time
// 98, the one whose req is not followed by gnt fails and nine pass. Before
// this the assertion read nothing and never ran either block.
TEST(GenericInterfacePortSim, AssertionSamplesThroughThePort) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface bus(input logic clk);\n"
                 "  logic req, gnt;\n"
                 "endinterface\n"
                 "module chk_generic(interface m);\n"
                 "  int p = 0, f = 0;\n"
                 "  assert property (@(posedge m.clk) m.req |=> m.gnt) "
                 "p++; else f++;\n"
                 "endmodule\n"
                 "module t;\n"
                 "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
                 "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
                 "  always @(negedge clk) begin av <= av << 1; bv <= bv "
                 "<< 1; end\n"
                 "  bus b(clk);\n"
                 "  assign b.req = av[0]; assign b.gnt = bv[0];\n"
                 "  chk_generic u2(b);\n"
                 "  initial #98 $display(\"p2=%0d f2=%0d\", u2.p, u2.f);\n"
                 "endmodule\n",
                 f),
      "p2=9 f2=1\n");
}

}  // namespace
