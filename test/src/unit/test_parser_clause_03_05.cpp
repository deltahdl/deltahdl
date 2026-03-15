// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, InterfaceInstantiationInModule) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "endinterface\n"
              "module top;\n"
              "  logic clk;\n"
              "  simple_bus sb_intf(.clk(clk));\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, InterfaceWithMixedContents) {
  EXPECT_TRUE(
      ParseOk("interface ifc #(parameter int W = 8) (input logic clk);\n"
              "  localparam int DEPTH = 4;\n"
              "  logic [W-1:0] data;\n"
              "  wire valid;\n"
              "  function automatic int xform(int v); return v; endfunction\n"
              "  task send; endtask\n"
              "  assign valid = |data;\n"
              "  modport master(output data, input valid);\n"
              "  modport slave(input data, output valid);\n"
              "endinterface\n"));
}

}  // namespace
