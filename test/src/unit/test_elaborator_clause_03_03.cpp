// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, ModuleWithMixedContents) {
  EXPECT_TRUE(
      ElabOk("module m (input logic clk, output logic [7:0] q);\n"
             "  wire [7:0] net;\n"
             "  logic [7:0] var;\n"
             "  localparam int HALF = 4;\n"
             "  assign net = var;\n"
             "  always_comb var = ~q;\n"
             "  always_ff @(posedge clk) q <= net;\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, ModuleWithSubroutineElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "  task do_nothing;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, ModuleWithModuleInstElaborates) {
  EXPECT_TRUE(
      ElabOk("module sub(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic x, y;\n"
             "  sub u0(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(DesignBuildingBlockElaboration, ModuleWithGenerateElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 1;\n"
             "  if (P) begin : gen\n"
             "    logic w;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ModuleDefinitions, EmptyModuleElaborates) {
  EXPECT_TRUE(ElabOk("module m; endmodule\n"));
}

TEST(ModuleDefinitions, ModuleAsContainer) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  wire b;\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

}  // namespace
