#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

uint64_t RunVerilog2005(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile(
      "<test>", "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

TEST(Verilog2005KeywordSimulation, AddedWordCarriesValuesAtRuntime) {
  auto result = RunVerilog2005(
      "module m;\n"
      "  reg  [7:0] src;\n"
      "  reg        en;\n"
      "  uwire [7:0] bus;\n"
      "  uwire       flag;\n"
      "  reg  [7:0] result;\n"
      "  assign bus  = src + 8'd1;\n"
      "  assign flag = en;\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    en  = 1'b1;\n"
      "    #1 result = flag ? bus + bus - 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog2005KeywordSimulation, AddedWordTypesAPortAtRuntime) {
  auto result = RunVerilog2005(
      "module child (input wire [7:0] a, output uwire [7:0] y);\n"
      "  assign y = a + a;\n"
      "endmodule\n"
      "module top;\n"
      "  reg   [7:0] src;\n"
      "  uwire [7:0] dst;\n"
      "  reg   [7:0] result;\n"
      "  child u1 (.a(src), .y(dst));\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = dst + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(Verilog2005KeywordSimulation,
     AddedWordTypesEveryDeclarationFormAtRuntime) {
  auto with_assignment = RunVerilog2005(
      "module m;\n"
      "  reg   [7:0] src;\n"
      "  uwire [7:0] bus = src + 8'd1;\n"
      "  reg   [7:0] result;\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = bus + bus - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(with_assignment, 43u);

  auto non_ansi = RunVerilog2005(
      "module ch (a, y);\n"
      "  input  [7:0] a;\n"
      "  output [7:0] y;\n"
      "  uwire  [7:0] y;\n"
      "  assign y = a + a;\n"
      "endmodule\n"
      "module top;\n"
      "  reg  [7:0] src;\n"
      "  wire [7:0] dst;\n"
      "  reg  [7:0] result;\n"
      "  ch u1 (src, dst);\n"
      "  initial begin\n"
      "    src = 8'd21;\n"
      "    #1 result = dst + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(non_ansi, 43u);
}

TEST(Verilog2005KeywordSimulation, IncludedVerilog1995RolesStillRun) {
  auto gates = RunVerilog2005(
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

  auto control = RunVerilog2005(
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

TEST(Verilog2005KeywordSimulation, IncludedAutomaticAndLocalparamStillRun) {
  auto result = RunVerilog2005(
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

TEST(Verilog2005KeywordSimulation, IncludedSignedAndUnsignedStillDiverge) {
  auto result = RunVerilog2005(
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

TEST(Verilog2005KeywordSimulation, ConstantFormsCarryValuesAtRuntime) {
  auto from_literal = RunVerilog2005(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunVerilog2005(
      "module m;\n"
      "  parameter P = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = P * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunVerilog2005(
      "module m;\n"
      "  localparam L = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = L * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);

  auto from_function = RunVerilog2005(
      "module m;\n"
      "  function automatic [7:0] twice(input reg [7:0] n);\n"
      "    twice = n + n;\n"
      "  endfunction\n"
      "  reg [7:0] result;\n"
      "  initial result = twice(8'd21) + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_function, 43u);
}

TEST(Verilog2005KeywordSimulation, ConstantFormsSizeDeclarationsAtRuntime) {
  const char* const kSrc =
      "module m;\n"
      "  parameter  P = 4;\n"
      "  localparam L = 4;\n"
      "  function automatic integer width_of(input reg [7:0] n);\n"
      "    width_of = n;\n"
      "  endfunction\n"
      "  reg [3:0]              from_literal;\n"
      "  reg [P-1:0]            from_parameter;\n"
      "  reg [L-1:0]            from_localparam;\n"
      "  reg [width_of(4)-1:0]  from_function;\n"
      "  reg [7:0]              result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    from_function   = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam - 8'd10;\n"
      "  end\n"
      "endmodule\n";

  EXPECT_EQ(RunVerilog2005(kSrc, "result"), 23u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_localparam"), 11u);
  EXPECT_EQ(RunVerilog2005(kSrc, "from_function"), 11u);
}

TEST(Verilog2005KeywordSimulation, UnlistedWordsRunAsIdentifiers) {
  auto result = RunVerilog2005(
      "module m;\n"
      "  reg [7:0] logic;\n"
      "  reg [7:0] bit;\n"
      "  reg [7:0] byte;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    logic  = 8'd21;\n"
      "    bit    = 8'd1;\n"
      "    byte   = 8'd0;\n"
      "    result = logic * 2 + bit + byte;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
