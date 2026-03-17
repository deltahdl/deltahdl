#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(FunctionalCoverageParsing, InterfaceClockingWithModport) {
  EXPECT_TRUE(
      ParseOk("interface bus_A (input clk);\n"
              "  logic [15:0] data;\n"
              "  logic write;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output write;\n"
              "  endclocking\n"
              "  modport test (input data, output write, input clk);\n"
              "  modport dut (output data, input write, input clk);\n"
              "endinterface\n"));
}

}  // namespace
