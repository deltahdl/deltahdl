// §23.2.4

#include "fixture_elaborator.h"

namespace {

TEST(ModuleContents, MixedItemsElaborate) {
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

TEST(ModuleContents, DeclarationsAndAssign) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  wire b;\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

}  // namespace
