// §30.4.1's module path destination, as a running simulation delays it: the
// path delay reaches the output port whatever drives the port inside the
// module.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A top module driving `a` 0, then 1 at 10 and 0 at 20, into `mybuf`'s `a` and
// printing each change of what it connects to `mybuf`'s `y` from 8 on, after
// the module `mybuf_decl` declares.
std::string BufferDesign(const std::string& mybuf_decl) {
  return mybuf_decl +
         "module top;\n"
         "  logic a;\n"
         "  wire ty;\n"
         "  mybuf u(.a(a), .y(ty));\n"
         "  always @(ty) if ($time >= 8) $display(\"t=%0t y=%b\", $time, ty);\n"
         "  initial begin\n"
         "    a = 0;\n"
         "    #10 a = 1;\n"
         "    #10 a = 0;\n"
         "  end\n"
         "endmodule\n";
}

// §30.4.1 (printed page 872): "The module path destination shall be a net or
// variable that is connected to a module output port or inout port", so an
// `output reg` written by `always @*` takes its path delay of 5. The delay
// reached only an output a continuous assignment drove, and y followed a at
// once.
TEST(ModulePathDestinationRun, ProcedureDrivenOutputTakesThePathDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture(BufferDesign("module mybuf(input a, output reg y);\n"
                                    "  always @* y = a;\n"
                                    "  specify\n"
                                    "    (a => y) = 5;\n"
                                    "  endspecify\n"
                                    "endmodule\n"),
                       f),
            "t=15 y=1\nt=25 y=0\n");
}

// The same for an output driven by a nested instance's output port.
TEST(ModulePathDestinationRun, NestedInstanceDrivenOutputTakesThePathDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture(BufferDesign("module leaf(input i, output o);\n"
                                    "  assign o = i;\n"
                                    "endmodule\n"
                                    "module mybuf(input a, output y);\n"
                                    "  leaf l(.i(a), .o(y));\n"
                                    "  specify\n"
                                    "    (a => y) = 5;\n"
                                    "  endspecify\n"
                                    "endmodule\n"),
                       f),
            "t=15 y=1\nt=25 y=0\n");
}

// §30.4.3 (printed page 874) on a flip-flop: `(posedge clk => (q +: d)) = (4,
// 6)` delays the q a clocked `q <= d` writes by 4 when it rises and 6 when it
// falls, both timed from the clock edge.
TEST(ModulePathDestinationRun, FlipFlopOutputTakesTheEdgePathDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module myff(input clk, input d, output reg q);\n"
                       "  always @(posedge clk) q <= d;\n"
                       "  specify\n"
                       "    (posedge clk => (q +: d)) = (4, 6);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk, d;\n"
                       "  wire tq;\n"
                       "  myff u(.clk(clk), .d(d), .q(tq));\n"
                       "  always @(tq) if ($time >= 8)\n"
                       "    $display(\"t=%0t q=%b\", $time, tq);\n"
                       "  initial begin\n"
                       "    clk = 0; d = 1;\n"
                       "    #10 clk = 1;\n"
                       "    #10 clk = 0;\n"
                       "    #5 d = 0;\n"
                       "    #5 clk = 1;\n"
                       "    #5 clk = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=14 q=1\nt=36 q=0\n");
}

}  // namespace
