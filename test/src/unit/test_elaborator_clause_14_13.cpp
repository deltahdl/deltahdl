#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InputSamplingElab, InputClockvarReadElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    @(cb);\n"
             "    $display(cb.data);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InputSamplingElab, InoutClockvarReadElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    @(cb);\n"
             "    $display(cb.data);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InputSamplingElab, ExplicitZeroSkewInputElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    input #0 data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(InputSamplingElab, MultipleInputSignalsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, b, c;\n"
             "  clocking cb @(posedge clk);\n"
             "    input a, b, c;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
