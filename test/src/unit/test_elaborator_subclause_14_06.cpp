#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SignalMultiBlockElab, SameSignalInTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking cb1 @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, SameSignalDifferentDirectionsElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking cb1 @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  clocking cb2 @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, SharedClockBlocksElaborate) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic a; clocking cb1 @(posedge clk);\n"
             "    input a;\n"
             "  endclocking\n"
             "  logic b; clocking cb2 @(posedge clk);\n"
             "    input b;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, InoutSignalInTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking cb1 @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(SignalMultiBlockElab, SameOutputSignalInTwoBlocksElaborates) {
  EXPECT_TRUE(
      ElabOk("module m; logic clk;\n"
             "  logic data; clocking cb1 @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  clocking cb2 @(negedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
