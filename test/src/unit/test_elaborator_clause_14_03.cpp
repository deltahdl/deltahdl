#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockingBlockElab, UnnamedNonDefaultBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, UnnamedDefaultBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  default clocking @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, WriteToInputClockvarError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.data = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, ReadFromOutputClockvarError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, InoutClockvarReadOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] bidir, result;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout bidir;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    result = cb.bidir;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClockingBlockElab, InoutClockvarWriteOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] bidir;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout bidir;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    cb.bidir = 8'hFF;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
