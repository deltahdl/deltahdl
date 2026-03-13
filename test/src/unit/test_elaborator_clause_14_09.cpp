#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClockingElab, ClockingInInterfaceElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus_if (input clk);\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endinterface\n"));
}

TEST(InterfaceClockingElab, InterfaceWithModportAndClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus_A (input clk);\n"
             "  logic [15:0] data;\n"
             "  logic write;\n"
             "  modport test (input data, output write, input clk);\n"
             "  modport dut (output data, input write, input clk);\n"
             "endinterface\n"));
}

TEST(InterfaceClockingElab, ClockingWithInterfaceHierExprElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge intf.clk);\n"
             "    input data = intf.data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
