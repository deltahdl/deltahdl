#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GenerateBlockContentSim, ModuleItemsOfEveryKindRunInsideAGenerateBlock) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module leafm(output logic [7:0] y);\n"
                 "  assign y = 8'd9;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  if (1) begin : g\n"
                 "    typedef logic [7:0] byte_t;\n"
                 "    class K;\n"
                 "      function int get(); return 11; endfunction\n"
                 "    endclass\n"
                 "    byte_t a;\n"
                 "    wire [7:0] w;\n"
                 "    logic [7:0] y;\n"
                 "    leafm u(.y(y));\n"
                 "    function automatic int f(int x);\n"
                 "      return x * 3;\n"
                 "    endfunction\n"
                 "    task automatic t(output int o); o = 13; endtask\n"
                 "    assign w = 8'd4;\n"
                 "    always_comb a = w + 8'd1;\n"
                 "    for (genvar k = 0; k < 2; k++) begin : n\n"
                 "      localparam int Q = k + 20;\n"
                 "    end\n"
                 "    initial begin\n"
                 "      int o;\n"
                 "      K kk;\n"
                 "      kk = new;\n"
                 "      t(o);\n"
                 "      #1;\n"
                 "      $display(\"%0d %0d %0d %0d %0d\", a, y, f(2), o,\n"
                 "               kk.get());\n"
                 "    end\n"
                 "  end\n"
                 "  initial #2 $display(\"%0d\", g.n[1].Q);\n"
                 "endmodule\n",
                 f),
      "5 9 6 13 11\n21\n");
}

TEST(GenerateBlockContentSim, InterfaceAndProgramGenerateBlocksHoldItems) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ii;\n"
                       "  if (1) begin : g\n"
                       "    function automatic int f(int x);\n"
                       "      return x + 40;\n"
                       "    endfunction\n"
                       "    initial $display(\"i %0d\", f(1));\n"
                       "  end\n"
                       "endinterface\n"
                       "program pp;\n"
                       "  if (1) begin : g\n"
                       "    function automatic int f(int x);\n"
                       "      return x + 50;\n"
                       "    endfunction\n"
                       "    initial $display(\"p %0d\", f(2));\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  ii u();\n"
                       "  pp v();\n"
                       "endmodule\n",
                       f),
            "i 41\np 52\n");
}

TEST(GenerateBlockContentSim,
     ADefparamLeavesAGenerateBlockParameterOfTheSameNameAsDeclared) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module c;\n"
                 "  parameter int P = 1;\n"
                 "  if (1) begin : g\n"
                 "    parameter int P = 3;\n"
                 "  end\n"
                 "  for (genvar k = 0; k < 1; k++) begin : h\n"
                 "    parameter int P = 4;\n"
                 "  end\n"
                 "  initial $display(\"m %0d %0d %0d\", P, g.P, h[0].P);\n"
                 "endmodule\n"
                 "interface ii;\n"
                 "  parameter int P = 1;\n"
                 "  if (1) begin : g\n"
                 "    parameter int P = 3;\n"
                 "  end\n"
                 "  initial $display(\"i %0d %0d\", P, g.P);\n"
                 "endinterface\n"
                 "module top;\n"
                 "  c u();\n"
                 "  ii v();\n"
                 "  defparam u.P = 5;\n"
                 "  defparam v.P = 7;\n"
                 "endmodule\n",
                 f),
      "m 5 3 4\ni 7 3\n");
}

TEST(GenerateBlockContentSim,
     ADefparamLeavesAProgramGenerateBlockParameterOfTheSameName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program pp;\n"
                       "  parameter int P = 1;\n"
                       "  if (1) begin : g\n"
                       "    parameter int P = 3;\n"
                       "  end\n"
                       "  initial $display(\"p %0d %0d\", P, g.P);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  pp w();\n"
                       "  defparam w.P = 7;\n"
                       "endmodule\n",
                       f),
            "p 7 3\n");
}

}  // namespace
