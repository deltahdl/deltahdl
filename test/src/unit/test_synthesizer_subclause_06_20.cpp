#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

namespace {

// §6.20 makes a parameter a constant fixed at elaboration, so a parameter read
// as an operand stands for its value. Each case fails on a lowering that looks
// an operand up among the module's ports, variables and nets alone. That
// lowering reads each bit of the parameter as constant zero, and reports a
// parameter read as a truth value as an operand with no width. Every value of
// `a` is driven, and each case takes a parameter value whose low bit is zero,
// so reading the parameter as zero, or its truth value from bit 0 alone, gives
// a different output.

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

// A.2.1.1's param_assignment gives a parameter unpacked dimensions, and §10.9.1
// assigns a positional pattern to an unpacked array from its left bound on.
// Each case fails on a lowering that reads an element of the parameter as
// constant zero. The descending range also fails on one that puts the pattern's
// first element at the lowest address.

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

// A parameter whose value the synthesizer cannot record as constant bits is
// reported where an operand names it. Each case fails on a lowering that reads
// such a parameter as constant zero and answers a netlist.

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
