#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

uint64_t Run1995(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

TEST(Verilog1995KeywordSimulation, FreedWordsRunAcrossAHierarchy) {
  auto result = Run1995(
      "module bit (input wire [7:0] logic, output wire [7:0] byte);\n"
      "  parameter int = 2;\n"
      "  assign byte = logic * int;\n"
      "endmodule\n"
      "module top;\n"
      "  reg  [7:0] string;\n"
      "  wire [7:0] longint;\n"
      "  reg  [7:0] result;\n"
      "  bit interface (.logic(string), .byte(longint));\n"
      "  task shortint; begin result = longint + 8'd1; end endtask\n"
      "  initial begin\n"
      "    string = 8'd21;\n"
      "    #1 shortint;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog1995KeywordSimulation, ReservedGateAndNetKeywordsDriveValues) {
  auto result = Run1995(
      "module m;\n"
      "  reg  a, b;\n"
      "  wire y, z;\n"
      "  wand w;\n"
      "  reg [7:0] result;\n"
      "  and g1 (y, a, b);\n"
      "  nor g2 (z, a, b);\n"
      "  assign w = a;\n"
      "  assign w = b;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    #1 result = {5'd0, y, z, w};\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 5u);
}

TEST(Verilog1995KeywordSimulation, ReservedProceduralKeywordsRun) {
  auto result = Run1995(
      "module m;\n"
      "  integer i;\n"
      "  reg [7:0] result;\n"
      "  reg [1:0] sel;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    for (i = 0; i < 4; i = i + 1) result = result + 8'd5;\n"
      "    repeat (2) result = result + 8'd5;\n"
      "    i = 2;\n"
      "    while (i > 0) begin\n"
      "      result = result + 8'd1;\n"
      "      i = i - 1;\n"
      "    end\n"
      "    sel = 2'b10;\n"
      "    casez (sel)\n"
      "      2'b1?: result = result + 8'd1;\n"
      "      default: result = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

TEST(Verilog1995KeywordSimulation, ReservedEventControlAndBranchRun) {
  auto result = Run1995(
      "module m;\n"
      "  reg clk, rst;\n"
      "  reg [7:0] result;\n"
      "  always @(posedge clk or negedge rst)\n"
      "    if (!rst) result <= 8'd40;\n"
      "    else result <= result + 8'd1;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    rst = 1'b1;\n"
      "    #1 rst = 1'b0;\n"
      "    #1 rst = 1'b1;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 clk = 1'b0;\n"
      "    #1 clk = 1'b1;\n"
      "    #1 clk = 1'b0;\n"
      "    #1 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog1995KeywordSimulation, WaitForeverAndDisableRun) {
  auto result = Run1995(
      "module m;\n"
      "  reg go;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    go = 1'b0;\n"
      "    #2 go = 1'b1;\n"
      "  end\n"
      "  initial begin : blk\n"
      "    result = 8'd40;\n"
      "    wait (go);\n"
      "    forever begin\n"
      "      result = result + 8'd1;\n"
      "      if (result == 8'd43) disable blk;\n"
      "      #1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog1995KeywordSimulation, FunctionAndDefparamRun) {
  auto result = Run1995(
      "module sub (output wire [7:0] o);\n"
      "  parameter p = 1;\n"
      "  assign o = p;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  reg  [7:0] result;\n"
      "  sub u (w);\n"
      "  defparam u.p = 21;\n"
      "  function [7:0] twice;\n"
      "    input x;\n"
      "    twice = x ? 8'd2 : 8'd0;\n"
      "  endfunction\n"
      "  initial #1 result = w * twice(1'b1) + 8'd1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog1995KeywordSimulation, FreedWordNamesAnEventDrivingAProcess) {
  auto result = Run1995(
      "module m;\n"
      "  event logic;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd40;\n"
      "    #1 -> logic;\n"
      "  end\n"
      "  always @(logic) result = result + 8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog1995KeywordSimulation, LiteralAndParameterConstantsAgree) {
  auto from_literal = Run1995(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = Run1995(
      "module m;\n"
      "  parameter P = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_freed_name = Run1995(
      "module m;\n"
      "  parameter int = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = int * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_freed_name, 43u);
}

TEST(Verilog1995KeywordSimulation, ForceAndReleaseRun) {
  auto result = Run1995(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    v = 8'd1;\n"
      "    force v = 8'd43;\n"
      "    #1 result = v;\n"
      "    release v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
