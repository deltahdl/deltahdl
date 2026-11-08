#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
