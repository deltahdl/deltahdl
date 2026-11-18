#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceModportClockingSim,
     TheProgramDrivesEachBusThroughItsClockingBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "interface A_Bus(input logic clk);\n"
                "  wire req, gnt;\n"
                "  wire [7:0] addr, data;\n"
                "  clocking sb @(posedge clk);\n"
                "    input gnt;\n"
                "    output req, addr;\n"
                "    inout data;\n"
                "    property p1; req ##[1:3] gnt; endproperty\n"
                "  endclocking\n"
                "  modport DUT(input clk, req, addr, output gnt, inout data);\n"
                "  modport STB(clocking sb);\n"
                "  modport TB(input gnt, output req, addr, inout data);\n"
                "endinterface\n"
                "module dev1(A_Bus.DUT b);\n"
                "  logic g = 0;\n"
                "  assign b.gnt = g;\n"
                "  always @(posedge b.clk) g <= (b.req === 1);\n"
                "  always @(negedge b.req) $display(\"%0t %m saw %h %h\", "
                "$time, b.addr, b.data);\n"
                "endmodule\n"
                "module dev2(A_Bus.DUT b);\n"
                "  logic g = 0;\n"
                "  assign b.gnt = g;\n"
                "  always @(posedge b.clk) g <= (b.req === 1);\n"
                "  always @(negedge b.req) $display(\"%0t %m saw %h %h\", "
                "$time, b.addr, b.data);\n"
                "endmodule\n"
                "program T(A_Bus.STB b1, A_Bus.STB b2);\n"
                "  typedef virtual A_Bus.STB SYNCTB;\n"
                "  task request(SYNCTB s);\n"
                "    s.sb.req <= 1;\n"
                "  endtask\n"
                "  task wait_grant(SYNCTB s);\n"
                "    wait (s.sb.gnt == 1);\n"
                "  endtask\n"
                "  task drive(SYNCTB s, logic [7:0] adr, data);\n"
                "    if (s.sb.gnt == 0) begin\n"
                "      request(s);\n"
                "      wait_grant(s);\n"
                "    end\n"
                "    s.sb.addr <= adr;\n"
                "    s.sb.data <= data;\n"
                "    repeat (2) @s.sb;\n"
                "    s.sb.req <= 0;\n"
                "  endtask\n"
                "  assert property (b1.sb.p1) else $display(\"%0t p1 failed\", "
                "$time);\n"
                "  initial begin\n"
                "    @(b1.sb);\n"
                "    drive(b1, 8'h12, 8'h34);\n"
                "    $display(\"%0t b1 done\", $time);\n"
                "    drive(b2, 8'h56, 8'h78);\n"
                "    $display(\"%0t b2 done\", $time);\n"
                "  end\n"
                "endprogram\n"
                "module top;\n"
                "  logic clk = 0;\n"
                "  initial repeat (30) #5 clk = ~clk;\n"
                "  A_Bus b1(clk);\n"
                "  A_Bus b2(clk);\n"
                "  dev1 d1(b1);\n"
                "  dev2 d2(b2);\n"
                "  T tb(b1, b2);\n"
                "endmodule\n",
                f),
            "5 p1 failed\n45 b1 done\n45 top.d1 saw 12 34\n55 p1 failed\n"
            "65 p1 failed\n75 p1 failed\n85 p1 failed\n85 b2 done\n"
            "85 top.d2 saw 56 78\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
