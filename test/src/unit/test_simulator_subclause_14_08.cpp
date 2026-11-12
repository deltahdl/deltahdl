#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

TEST(MultipleClockingBlocksSim, DISABLED_TheClauseProgramRunsAgainstItsDut) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture(
          "`timescale 1ns/1ps\n"
          "program test(input phi1, input [15:0] data, output logic write,\n"
          "             input phi2, inout [8:1] cmd, input enable);\n"
          "  reg [8:1] cmd_reg;\n"
          "  clocking cd1 @(posedge phi1);\n"
          "    input data;\n"
          "    output write;\n"
          "    input state = top.cpu1.state;\n"
          "  endclocking\n"
          "  clocking cd2 @(posedge phi2);\n"
          "    input #2 output #4ps cmd;\n"
          "    input enable;\n"
          "  endclocking\n"
          "  initial begin\n"
          "    cmd_reg = 8'h5a;\n"
          "    @(cd1);\n"
          "    $display(\"data=%h state=%0d\", cd1.data, cd1.state);\n"
          "    cd1.write <= 1;\n"
          "    @(cd2);\n"
          "    $display(\"cmd=%h enable=%b\", cd2.cmd, cd2.enable);\n"
          "    @(cd1);\n"
          "    $display(\"write=%b\", write);\n"
          "  end\n"
          "  assign cmd = enable ? cmd_reg : 'x;\n"
          "endprogram\n"
          "module cpu(input phi1, output logic [15:0] data, input write);\n"
          "  int state = 7;\n"
          "  initial data = 16'hbeef;\n"
          "endmodule\n"
          "module mem(input phi2, inout [8:1] cmd, output logic enable);\n"
          "  initial enable = 1;\n"
          "endmodule\n"
          "module top;\n"
          "  logic phi1 = 0, phi2 = 0;\n"
          "  wire [8:1] cmd;\n"
          "  logic [15:0] data;\n"
          "  always #5 phi1 = ~phi1;\n"
          "  initial #2 forever #5 phi2 = ~phi2;\n"
          "  test main (phi1, data, write, phi2, cmd, enable);\n"
          "  cpu cpu1 (phi1, data, write);\n"
          "  mem mem1 (phi2, cmd, enable);\n"
          "  initial #40 $finish;\n"
          "endmodule\n",
          f),
      "data=beef state=7\ncmd=5a enable=1\nwrite=1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
