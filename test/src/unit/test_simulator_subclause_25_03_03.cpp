#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
                 "  chk_generic u2(.m(b));\n"
                 "  initial #98 $display(\"p2=%0d f2=%0d\", u2.p, u2.f);\n"
                 "endmodule\n",
                 f),
      "p2=9 f2=1\n");
}

TEST(GenericInterfacePortSim, OneModuleBindsInstancesOfTwoInterfaceTypes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus_a; logic [7:0] d; endinterface\n"
                       "interface bus_b; logic [7:0] d; endinterface\n"
                       "module memMod(interface a);\n"
                       "  initial #1 $display(\"%m %0d\", a.d);\n"
                       "  task automatic put(input logic [7:0] v); a.d = v; "
                       "endtask\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus_a x(); bus_b y();\n"
                       "  memMod m1(.a(x)), m2(.a(y));\n"
                       "  initial begin\n"
                       "    x.d = 5; y.d = 9;\n"
                       "    #2 m2.put(33);\n"
                       "    #1 $display(\"x=%0d y=%0d\", x.d, y.d);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "top.m1 5\ntop.m2 9\nx=5 y=33\n");
}

TEST(GenericInterfacePortSim, InterfaceAndProgramHeadersBindTheInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus; logic [7:0] d; endinterface\n"
                       "interface wrap(interface p);\n"
                       "  initial #1 $display(\"wrap %0d\", p.d);\n"
                       "endinterface\n"
                       "program pr(interface q);\n"
                       "  initial #2 $display(\"prog %0d\", q.d);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  simple_bus b1(), b2();\n"
                       "  wrap w(.p(b1));\n"
                       "  pr p(.q(b2));\n"
                       "  initial begin b1.d = 42; b2.d = 17; end\n"
                       "endmodule\n",
                       f),
            "wrap 42\nprog 17\n");
}

}  // namespace
