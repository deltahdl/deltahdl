#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

namespace {

uint64_t RunClean(const std::string& src, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

TEST(KeywordVersionExampleSim, VerilogRegionRunsWithLogicAsAVariable) {
  auto result = RunClean(
      "`begin_keywords \"1364-2001\"\n"
      "module m2 (input wire clk, output wire [63:0] q);\n"
      "  reg [63:0] logic;\n"
      "  reg [63:0] result;\n"
      "  initial begin\n"
      "    logic = 64'd21;\n"
      "    result = logic * 2 + 1;\n"
      "  end\n"
      "  assign q = logic;\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(KeywordVersionExampleSim, VerilogRegionRunsWithLogicAsAnIntegerVariable) {
  auto result = RunClean(
      "`begin_keywords \"1364-2001\"\n"
      "module m2;\n"
      "  integer logic;\n"
      "  reg [63:0] result;\n"
      "  initial begin\n"
      "    logic = 21;\n"
      "    result = logic * 2 + 1;\n"
      "  end\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 43u);
}

TEST(KeywordVersionExampleSim, SystemVerilogRegionRunsTheInterface) {
  auto result = RunClean(
      "`begin_keywords \"1800-2005\"\n"
      "interface if1 (input wire clk);\n"
      "  wire [7:0] data;\n"
      "  assign data = 8'd33;\n"
      "endinterface\n"
      "`end_keywords\n"
      "module top;\n"
      "  wire c;\n"
      "  if1 u (.clk(c));\n"
      "  reg [7:0] result;\n"
      "  initial #1 result = u.data;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

TEST(KeywordVersionExampleSim, ModuleWithNoDirectiveRunsUnderTheDefaultList) {
  auto result = RunClean(
      "module m1;\n"
      "  logic [63:0] result;\n"
      "  initial result = 64'd21 * 2 + 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 43u);
}

}  // namespace
