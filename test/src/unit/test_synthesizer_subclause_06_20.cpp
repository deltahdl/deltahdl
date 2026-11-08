#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ParameterOperandSynthesis, ParameterInBitwiseExpressionIsItsValue) {
  ExpectInputSweep(
      "module m #(parameter P = 4'b1010)\n"
      "    (input [3:0] a, output logic [3:0] y);\n"
      "  assign y = a & P;\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0xAu; });
}

TEST(ParameterOperandSynthesis, LocalparamConditionSelectsByItsValue) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic [3:0] y);\n"
      "  localparam L = 2;\n"
      "  assign y = L ? a : 4'd0;\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a; });
}

TEST(ParameterOperandSynthesis, ParameterLogicalOperandIsItsTruthValue) {
  ExpectInputSweep(
      "module m #(parameter P = 2) (input [3:0] a, output logic y);\n"
      "  assign y = P && a;\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a != 0; });
}

TEST(ParameterOperandSynthesis, ParameterArrayElementIsItsPatternsElement) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic [3:0] y);\n"
      "  localparam logic [3:0] A [2] = '{4'b1010, 4'b0101};\n"
      "  assign y = a & A[0];\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0xAu; });
}

TEST(ParameterOperandSynthesis, DescendingParameterArrayStartsAtItsLeftBound) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic [3:0] y);\n"
      "  localparam logic [3:0] B [1:0] = '{4'b1010, 4'b0101};\n"
      "  assign y = a & B[0];\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a & 0x5u; });
}

TEST(ParameterOperandSynthesis, KeyedPatternParameterArrayIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  localparam logic [3:0] K [2] = '{default: 4'b1010};\n"
                   "  assign y = a & K[0];\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parameter's value has no lowering in the synthesizer", 3, "6.20"));
}

TEST(ParameterOperandSynthesis, RealParameterOperandIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  localparam real R = 2.0;\n"
                   "  assign y = a +\n"
                   "             R;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parameter's value has no lowering in the synthesizer", 4, "6.20"));
}

}  // namespace
