#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

uint64_t RunNoconfig(const std::string& body, const char* var_name) {
  SimFixture f;
  auto fid =
      f.mgr.AddFile("<test>", "`begin_keywords \"1364-2001-noconfig\"\n" +
                                  body + "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

TEST(NoconfigKeywordSimulation, ExcludedWordsRunAcrossAHierarchy) {
  auto result = RunNoconfig(
      "module cell (input wire [7:0] design, output wire [7:0] library);\n"
      "  parameter incdir = 2;\n"
      "  assign library = design * incdir;\n"
      "endmodule\n"
      "module top;\n"
      "  reg  [7:0] instance;\n"
      "  wire [7:0] liblist;\n"
      "  reg  [7:0] endconfig;\n"
      "  reg  [7:0] result;\n"
      "  cell config (.design(instance), .library(liblist));\n"
      "  task use; begin result = liblist + endconfig; end endtask\n"
      "  initial begin : include\n"
      "    instance = 8'd21;\n"
      "    endconfig = 8'd1;\n"
      "    #1 use;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(NoconfigKeywordSimulation, ExcludedWordNamesEventDrivingAProcess) {
  auto result = RunNoconfig(
      "module m;\n"
      "  event design;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd40;\n"
      "    #1 -> design;\n"
      "  end\n"
      "  always @(design) result = result + 8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(NoconfigKeywordSimulation, ExcludedWordsCarryConstantsAtRuntime) {
  auto from_literal = RunNoconfig(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial result = 8'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_literal, 43u);

  auto from_parameter = RunNoconfig(
      "module m;\n"
      "  parameter incdir = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = incdir * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_parameter, 43u);

  auto from_localparam = RunNoconfig(
      "module m;\n"
      "  localparam liblist = 21;\n"
      "  reg [7:0] result;\n"
      "  initial result = liblist * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(from_localparam, 43u);
}

TEST(NoconfigKeywordSimulation, ExcludedWordConstantsSizeADeclaration) {
  const char* const kSrc =
      "module m;\n"
      "  parameter  incdir  = 4;\n"
      "  localparam liblist = 4;\n"
      "  reg [3:0]          from_literal;\n"
      "  reg [incdir-1:0]   from_parameter;\n"
      "  reg [liblist-1:0]  from_localparam;\n"
      "  reg [7:0]          result;\n"
      "  initial begin\n"
      "    from_literal    = 8'h1B;\n"
      "    from_parameter  = 8'h1B;\n"
      "    from_localparam = 8'h1B;\n"
      "    result = from_literal + from_parameter + from_localparam + 8'd10;\n"
      "  end\n"
      "endmodule\n";

  EXPECT_EQ(RunNoconfig(kSrc, "result"), 43u);
  EXPECT_EQ(RunNoconfig(kSrc, "from_literal"), 11u);
  EXPECT_EQ(RunNoconfig(kSrc, "from_parameter"), 11u);
  EXPECT_EQ(RunNoconfig(kSrc, "from_localparam"), 11u);
}

TEST(NoconfigKeywordSimulation, KeptAutomaticAndLocalparamStillRun) {
  auto result = RunNoconfig(
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

TEST(NoconfigKeywordSimulation, KeptSignedAndUnsignedStillDiverge) {
  auto result = RunNoconfig(
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

TEST(NoconfigKeywordSimulation, ExcludedWordNamesASubroutineArgumentAtRuntime) {
  auto result = RunNoconfig(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  function [7:0] twice(input reg [7:0] library);\n"
      "    twice = library + library;\n"
      "  endfunction\n"
      "  task bump(input reg [7:0] incdir);\n"
      "    result = result + incdir;\n"
      "  endtask\n"
      "  initial begin\n"
      "    result = 8'd3;\n"
      "    bump(twice(8'd20));\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(NoconfigKeywordSimulation, InheritedKeywordRolesStillRun) {
  auto gates = RunNoconfig(
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

  auto control = RunNoconfig(
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

TEST(NoconfigKeywordSimulation, UnlistedWordsStillRunAsIdentifiers) {
  auto result = RunNoconfig(
      "module m;\n"
      "  reg [7:0] logic;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    logic = 8'd21;\n"
      "    result = logic * 2 + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
