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

// §14.6 lists inouts among the directions a signal may take across several
// clocking blocks; the same inout signal in two blocks elaborates cleanly.
TEST(SignalMultiBlockElab, InoutSignalInTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

// §14.6 lists outputs among the directions a signal may take across several
// clocking blocks; the same output signal in two blocks elaborates cleanly.
TEST(SignalMultiBlockElab, SameOutputSignalInTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb1 @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}
