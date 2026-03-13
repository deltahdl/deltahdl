#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SignalMultiBlockElab, SameSignalInTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, SameSignalDifferentDirectionsElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  clocking cb2 @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, SharedClockBlocksElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    input a;\n"
             "  endclocking\n"
             "  clocking cb2 @(posedge clk);\n"
             "    input b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, ClockSignalSharedAcrossBlocks) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    input a;\n"
             "  endclocking\n"
             "  clocking cb2 @(posedge clk);\n"
             "    output a;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
