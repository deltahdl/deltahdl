#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceNamedBundleSim, VariableAccessThroughPortSharesInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  initial #1 a.gnt = a.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(sb_intf);\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

TEST(InterfaceNamedBundleSim, NetDrivenThroughPortReachesSharedNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  wire [7:0] data;\n"
      "endinterface\n"
      "module driver(simple_bus a);\n"
      "  assign a.data = 8'hA5;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  driver d(sb_intf);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.data", 0xA5u}});
}

TEST(InterfaceNamedBundleSim, VectorVariableAccessThroughPortSharesInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic [7:0] addr;\n"
      "  logic [7:0] snoop;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  initial #1 a.snoop = a.addr;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(sb_intf);\n"
      "  initial sb_intf.addr = 8'h3C;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.snoop", 0x3Cu}});
}

TEST(InterfaceNamedBundleSim, ScalarNetDrivenThroughPortReachesSharedNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  wire valid;\n"
      "endinterface\n"
      "module driver(simple_bus a);\n"
      "  assign a.valid = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  driver d(sb_intf);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.valid", 1u}});
}

TEST(InterfaceNamedBundleSim, VariableRefAccessViaNamedConnection) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  initial #1 a.gnt = a.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.a(sb_intf));\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

TEST(InterfaceNamedBundleSim, VariableRefAccessViaImplicitConnection) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus sb_intf);\n"
      "  initial #1 sb_intf.gnt = sb_intf.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.sb_intf);\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

TEST(InterfaceNamedBundleSim, VariableRefAccessViaWildcardConnection) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus sb_intf);\n"
      "  initial #1 sb_intf.gnt = sb_intf.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.*);\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

TEST(InterfaceNamedBundleSim, TheInterfacesOwnPortIsReachedThroughThePort) {
  SimFixture f;
  std::string out = RunCapture(
      "interface A_Bus(input logic clk);\n"
      "  logic req;\n"
      "  modport DUT(input clk, input req);\n"
      "endinterface\n"
      "module dev(A_Bus b);\n"
      "  int n = 0;\n"
      "  always @(posedge b.clk) n++;\n"
      "endmodule\n"
      "module mdev(A_Bus.DUT b);\n"
      "  int n = 0;\n"
      "  always @(posedge b.clk) n++;\n"
      "  initial #7 $display(\"clk=%b\", b.clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  A_Bus b2(clk);\n"
      "  dev d(b2);\n"
      "  mdev m(b2);\n"
      "  initial #28 begin $display(\"n=%0d m=%0d\", d.n, m.n); $finish; end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "clk=1\nn=3 m=3\n$finish at time 28\n");
}

}  // namespace
