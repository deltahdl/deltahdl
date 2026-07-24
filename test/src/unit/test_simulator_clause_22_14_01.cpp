#include "helpers_preprocess_and_get.h"

namespace {

// Runs the full preprocess -> parse -> elaborate -> simulate pipeline on `src`
// and returns the final value of `var_name`, insisting that nothing along the
// way reported a diagnostic. The error check matters here: the examples that
// §22.14.1 says are legal must run clean, not merely produce a number after
// the front end recovered from a rejected declaration.
uint64_t RunClean(const std::string& src, const char* var_name) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  auto value = RunPreprocessedSim(f, fid, var_name, pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  return value;
}

// §22.14.1's second example run to completion. Inside a 1364-2001 region the
// module's 64-bit variable is named `logic`; here it is written and then read
// back as an operand, so the value observed at the end of the run shows the
// word carried a real variable at runtime rather than only surviving parsing
// and elaboration.
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

// The same example at runtime with the variable declared as an `integer`
// rather than the packed `reg` the LRM prints. The freed identifier has to
// carry a value through a different storage path, and it is written and read
// back here just as the packed form is above.
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

// §22.14.1's fourth example run to completion. The interface declared inside
// the 1800-2005 region is instantiated by a module outside the pair, and the
// value driven inside the interface reaches the instantiating module — the
// design element the region governs is a working one, not merely a parseable
// one.
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

// §22.14.1's first example run to completion: with no `begin_keywords anywhere
// the implementation's default reserved word list applies, and this
// implementation's default reserves `logic` as a type keyword. The module both
// compiles and computes under that list.
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
