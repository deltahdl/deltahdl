#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

uint64_t Run2001(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

TEST(Verilog2001KeywordSimulation, LiteralParameterAndLocalparamAgree) {
  auto from_literal = Run2001(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = Run2001(
      "module m;\n"
      "  parameter P = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = Run2001(
      "module m;\n"
      "  localparam L = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);
}

TEST(Verilog2001KeywordSimulation, AutomaticFunctionAndTaskRun) {
  auto result = Run2001(
      "module m;\n"
      "  localparam L = 20;\n"
      "  reg [7:0] result;\n"
      "  function automatic [7:0] fact(input reg [7:0] n);\n"
      "    begin\n"
      "      if (n <= 1) fact = 8'd1;\n"
      "      else fact = n * fact(n - 1);\n"
      "    end\n"
      "  endfunction\n"
      "  task automatic bump(input reg [7:0] d);\n"
      "    result = result + d;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = L;\n"
      "    bump(fact(8'd3));\n"
      "    bump(8'd17);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog2001KeywordSimulation, SignedDeclarationsChangeTheArithmetic) {
  auto result = Run2001(
      "module m;\n"
      "  reg signed [7:0] a, b;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    a = -8'sd7;\n"
      "    b = 8'sd6;\n"
      "    result = -(a * b) + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog2001KeywordSimulation, SignedAndUnsignedDeclarationsDiverge) {
  auto result = Run2001(
      "module m;\n"
      "  reg signed   [7:0] s;\n"
      "  reg unsigned [7:0] u;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    s = 8'hF8;\n"
      "    u = 8'hF8;\n"
      "    result = (s < 0 ? 8'd40 : 8'd0) + (u < 8'd1 ? 8'd0 : 8'd3);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog2001KeywordSimulation, SignedNetKeepsItsSignednessAtRuntime) {
  auto result = Run2001(
      "module m;\n"
      "  reg  signed [7:0] d;\n"
      "  wire signed [7:0] w;\n"
      "  reg  [7:0] result;\n"
      "  assign w = d;\n"
      "  initial begin\n"
      "    d = 8'hF8;\n"
      "    #1 result = (w < 0) ? 8'd43 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog2001KeywordSimulation, ConstantFormsAllSizeADeclaration) {
  const char* const kSrc =
      "module m;\n"
      "  parameter  P = 4;\n"
      "  localparam L = 4;\n"
      "  reg [3:0]   from_literal;\n"
      "  reg [P-1:0] from_parameter;\n"
      "  reg [L-1:0] from_localparam;\n"
      "  reg [7:0]   result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam + 8'd10;\n"
      "  end\n"
      "endmodule\n";

  EXPECT_EQ(Run2001(kSrc, "result"), 43u);
  EXPECT_EQ(Run2001(kSrc, "from_literal"), 11u);
  EXPECT_EQ(Run2001(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(Run2001(kSrc, "from_localparam"), 11u);
}

TEST(Verilog2001KeywordSimulation, InheritedKeywordsStillRun) {
  auto gates = Run2001(
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
  EXPECT_EQ(gates, 5u);

  auto control = Run2001(
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
  EXPECT_EQ(control, 33u);
}

TEST(Verilog2001KeywordSimulation, InheritedEventControlAndBranchRun) {
  auto result = Run2001(
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

TEST(Verilog2001KeywordSimulation, FreedWordsRunAcrossAHierarchy) {
  auto result = Run2001(
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

TEST(Verilog2001KeywordSimulation, FreedWordNamesAnEventDrivingAProcess) {
  auto result = Run2001(
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

}  // namespace
