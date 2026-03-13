#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceClockingParse, ClockingBlockInInterface) {
  EXPECT_TRUE(
      ParseOk("interface bus_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

TEST(InterfaceClockingParse, InterfaceWithModportAndClocking) {
  EXPECT_TRUE(
      ParseOk("interface bus_A (input clk);\n"
              "  logic [15:0] data;\n"
              "  logic write;\n"
              "  modport test (input data, output write, input clk);\n"
              "  modport dut (output data, input write, input clk);\n"
              "endinterface\n"));
}

TEST(InterfaceClockingParse, ProgramWithInterfacePortsAndClocking) {
  EXPECT_TRUE(
      ParseOk("program test_prog(bus_A.test a, bus_B.test b);\n"
              "  reg [8:1] cmd_reg;\n"
              "  clocking cd1 @(posedge a.clk);\n"
              "    input data = a.data;\n"
              "    output write = a.write;\n"
              "    input state = top.cpu1.state;\n"
              "  endclocking\n"
              "  clocking cd2 @(posedge b.clk);\n"
              "    input #2 output #4ps cmd = b.cmd;\n"
              "    input en = b.enable;\n"
              "  endclocking\n"
              "endprogram\n"));
}

TEST(InterfaceClockingParse, ClockingSignalFromInterfaceHierPath) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge intf.clk);\n"
      "    input data = intf.data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
  EXPECT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

TEST(InterfaceClockingParse, TwoInterfacesWithModports) {
  EXPECT_TRUE(
      ParseOk("interface bus_A (input clk);\n"
              "  logic [15:0] data;\n"
              "  logic write;\n"
              "  modport test (input data, output write, input clk);\n"
              "  modport dut (output data, input write, input clk);\n"
              "endinterface\n"
              "interface bus_B (input clk);\n"
              "  logic [8:1] cmd;\n"
              "  logic enable;\n"
              "  modport test (input enable, input clk, inout cmd);\n"
              "  modport dut (output enable, input clk, input cmd);\n"
              "endinterface\n"));
}

}  // namespace
