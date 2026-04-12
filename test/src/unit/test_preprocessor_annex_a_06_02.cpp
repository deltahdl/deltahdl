#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ProceduralBlockPreprocessor, InitialBlock) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  initial a = 0;\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, AlwaysCombBlock) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, AlwaysFFBlock) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, FinalBlock) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, MacroExpandedAssignmentRhs) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define INIT_VAL 0\n"
      "module m;\n"
      "  initial a = `INIT_VAL;\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, ConditionalCompilationAroundBlock) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define USE_INIT\n"
      "module m;\n"
      "`ifdef USE_INIT\n"
      "  initial a = 0;\n"
      "`endif\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, MacroExpandedBlockBody) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define ASSIGN_A a = 1\n"
      "module m;\n"
      "  initial `ASSIGN_A;\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, CompoundAssignment) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "    b -= 2;\n"
      "    c *= 3;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, NonblockingAssignment) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n"));
}

TEST(ProceduralBlockPreprocessor, ConditionalCompilationAlwaysVariant) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define USE_FF\n"
      "module m;\n"
      "  logic clk, d, q;\n"
      "`ifdef USE_FF\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "`else\n"
      "  always_latch if (clk) q <= d;\n"
      "`endif\n"
      "endmodule\n"));
}

}  // namespace
