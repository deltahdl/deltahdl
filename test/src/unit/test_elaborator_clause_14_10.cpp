#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingBlockEventElab, AlwaysAtBlockNameElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking dram @(posedge phi1);\n"
             "    input data;\n"
             "    output negedge #1 address;\n"
             "  endclocking\n"
             "  always @(dram)\n"
             "    $display(\"triggered\");\n"
             "endmodule\n"));
}

TEST(ClockingBlockEventElab, PosedgeAndBlockEventBothElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking dram @(posedge phi1);\n"
             "    input data;\n"
             "  endclocking\n"
             "  always @(posedge phi1) $display(\"clock\");\n"
             "  always @(dram) $display(\"block event\");\n"
             "endmodule\n"));
}

TEST(ClockingBlockEventElab, InitialBlockWaitsOnEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input v;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    @(cb);\n"
             "    $display(cb.v);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
