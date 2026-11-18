#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(ParameterizedInterfaceSim, ABodyParameterIsRedefinedByNameAndByPosition) {
  EXPECT_EQ(
      RunWithoutErrors("interface ifc;\n"
                       "  parameter int W = 8;\n"
                       "  logic [W-1:0] data;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  ifc d();\n"
                       "  ifc #(.W(20)) n();\n"
                       "  ifc #(6) p();\n"
                       "  initial $display(\"%0d %0d %0d\", $bits(d.data), "
                       "$bits(n.data), $bits(p.data));\n"
                       "endmodule\n"),
      "8 20 6\n");
}

constexpr const char* kSimpleBus =
    "interface simple_bus #(AWIDTH = 8, DWIDTH = 8) (input logic clk);\n"
    "  logic [AWIDTH-1:0] addr;\n"
    "  logic [DWIDTH-1:0] data;\n"
    "  modport target(input addr, clk, ref data);\n"
    "endinterface\n";

TEST(ParameterizedInterfaceSim,
     EachOverrideLeavesTheOtherParameterAtItsDefault) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSimpleBus) +
                             "module top;\n"
                             "  logic clk = 1;\n"
                             "  simple_bus sb(clk);\n"
                             "  simple_bus #(.DWIDTH(16)) wide(clk);\n"
                             "  simple_bus #(4) pos(clk);\n"
                             "  initial #1 $display(\"%0d/%0d %0d/%0d %0d/%0d "
                             "%b\", $bits(sb.addr), $bits(sb.data), "
                             "$bits(wide.addr), $bits(wide.data), "
                             "$bits(pos.addr), $bits(pos.data), wide.clk);\n"
                             "endmodule\n"),
            "8/8 8/16 4/8 1\n");
}

TEST(ParameterizedInterfaceSim, AGenericPortSeesItsOwnInstancesWidths) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSimpleBus) +
                             "module memMod(interface a);\n"
                             "  initial #1 $display(\"%m %0d %0d %b\", "
                             "$bits(a.addr), $bits(a.data), a.clk);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  logic clk = 1;\n"
                             "  simple_bus sb(clk);\n"
                             "  simple_bus #(.DWIDTH(16)) wide(clk);\n"
                             "  simple_bus #(4) pos(clk);\n"
                             "  memMod m1(sb.target), m2(wide.target), "
                             "m3(pos.target);\n"
                             "endmodule\n"),
            "top.m1 8 8 1\ntop.m2 8 16 1\ntop.m3 4 8 1\n");
}

TEST(ParameterizedInterfaceSim,
     APortNamingTheInterfaceTakesAnyParameterization) {
  EXPECT_EQ(
      RunWithoutErrors("interface ifc #(W = 8);\n"
                       "  logic [W-1:0] data;\n"
                       "endinterface\n"
                       "module m(ifc a);\n"
                       "  initial #1 $display(\"%m %0d\", $bits(a.data));\n"
                       "endmodule\n"
                       "module top;\n"
                       "  ifc d();\n"
                       "  ifc #(3) n();\n"
                       "  m x(d), y(n);\n"
                       "endmodule\n"),
      "top.x 8\ntop.y 3\n");
}

TEST(ParameterizedInterfaceSim, AnInstanceInAGenerateBlockTakesTheGenvar) {
  EXPECT_EQ(RunWithoutErrors("interface ifc #(W = 8);\n"
                             "  logic [W-1:0] data;\n"
                             "endinterface\n"
                             "module top;\n"
                             "  for (genvar g = 1; g <= 2; g++) begin : gen\n"
                             "    ifc #(g * 4) i();\n"
                             "  end\n"
                             "  initial $display(\"%0d %0d\", "
                             "$bits(gen[1].i.data), $bits(gen[2].i.data));\n"
                             "endmodule\n"),
            "4 8\n");
}

TEST(ParameterizedInterfaceSim,
     AnInterfacePassesItsParameterToANestedInstance) {
  EXPECT_EQ(RunWithoutErrors("interface inner #(W = 8);\n"
                             "  logic [W-1:0] data;\n"
                             "endinterface\n"
                             "interface outer #(W = 8);\n"
                             "  inner #(W * 2) in();\n"
                             "  inner keep();\n"
                             "endinterface\n"
                             "module top;\n"
                             "  outer #(5) o();\n"
                             "  outer d();\n"
                             "  initial $display(\"%0d %0d %0d\", "
                             "$bits(o.in.data), $bits(o.keep.data), "
                             "$bits(d.in.data));\n"
                             "endmodule\n"),
            "10 8 16\n");
}

constexpr const char* kSizedTask =
    "interface ifc #(W = 8);\n"
    "  task rd(input logic [W-1:0] r);\n"
    "    $display(\"%0d %h\", $bits(r), r);\n"
    "  endtask\n"
    "  modport mp(import task rd(input logic [W-1:0] r));\n"
    "  initial #2 rd(16'hffff);\n"
    "endinterface\n";

TEST(ParameterizedInterfaceSim, AParameterSizedFormalTakesItsWidthInside) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSizedTask) + "module top;\n"
                                                       "  ifc i8();\n"
                                                       "  ifc #(12) i12();\n"
                                                       "endmodule\n"),
            "8 ff\n12 fff\n");
}

TEST(ParameterizedInterfaceSim,
     DISABLED_AParameterSizedFormalTakesTheCalleeInstancesWidthFromOutside) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSizedTask) +
                             "module u(ifc.mp b);\n"
                             "  initial b.rd(16'hffff);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ifc i8();\n"
                             "  ifc #(12) i12();\n"
                             "  u a(i8.mp), c(i12.mp);\n"
                             "  initial #1 begin i8.rd(16'hffff); "
                             "i12.rd(16'hffff); end\n"
                             "endmodule\n"),
            "8 ff\n12 fff\n8 ff\n12 fff\n8 ff\n12 fff\n");
}

}  // namespace
