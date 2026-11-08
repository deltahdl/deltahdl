#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_assign.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ConcatenationSynthesis, ConcatenationPlacesEachOperandAtItsOwnOffset) {
  ExpectInputSweep(
      "module m(input [2:0] a, input [1:0] b, output logic [4:0] y);\n"
      "  assign y = {a, b};\n"
      "endmodule\n",
      32, [](uint64_t v) {
        uint64_t a = v & 0x7u;
        uint64_t b = (v >> 3) & 0x3u;
        return (a << 2) | b;
      });
}

TEST(ConcatenationSynthesis, ConcatenatedLiteralCarriesItsOwnBits) {
  ExpectInputSweep(
      "module m(input [2:0] a, output logic [4:0] y);\n"
      "  assign y = {a, 2'b10};\n"
      "endmodule\n",
      8, [](uint64_t a) { return (a << 2) | 2u; });
}

TEST(ConcatenationSynthesis, NestedConcatenationJoinsAsOneVector) {
  ExpectInputSweep(
      "module m(input [2:0] a, input b, input c, output logic [4:0] y);\n"
      "  assign y = {a, {b, c}};\n"
      "endmodule\n",
      32, [](uint64_t v) {
        uint64_t a = v & 0x7u;
        uint64_t b = (v >> 3) & 0x1u;
        uint64_t c = (v >> 4) & 0x1u;
        return (a << 2) | (b << 1) | c;
      });
}

TEST(ConcatenationSynthesis, AnOperandOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [7:0] y);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  assign y = {g(a), a};\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concatenation operand has no width", 3,
                            "11.4.12"));
}

TEST(ConcatenationSynthesis, AnOperatorOverAnOperandOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [7:0] y, "
                   "output logic [7:0] z);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  assign y = {g(a) + a, a};\n"
                   "  assign z = {a + g(a), a};\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concatenation operand has no width", 3,
                            "11.4.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concatenation operand has no width", 4,
                            "11.4.12"));
}

TEST(ConcatenationSynthesis, AShiftOperandKeepsItsOwnSizeAndType) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input signed [3:0] a",
                        "{a >>> 1, 4'b0}"),
      1, [](uint64_t a, uint64_t) -> uint64_t {
        return ((a >> 1) | (a & 0x8u)) << 4;
      });
}

TEST(ConcatenationSynthesis, AnOperatorOperandIsAsLongAsItsLongerOperand) {
  ExpectInputSweep(
      "module m(input [7:0] a, output logic [8:0] y);\n"
      "  assign y = {a | 4'b0000, 1'b0};\n"
      "endmodule\n",
      256, [](uint64_t a) -> uint64_t { return a << 1; });
}

TEST(ConcatenationSynthesis, ASumOfTwoNamesIsAsLongAsTheLongerName) {
  ExpectInputSweep(
      "module m(input [2:0] a, input [1:0] b, output logic [6:0] y);\n"
      "  assign y = {a + b, a};\n"
      "endmodule\n",
      32, [](uint64_t v) -> uint64_t {
        uint64_t a = v & 0x7u;
        uint64_t b = (v >> 3) & 0x3u;
        return (((a + b) & 0x7u) << 3) | a;
      });
}

TEST(ConcatenationSynthesis, AComplementIsAsLongAsItsOperand) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a", "{~a, 1'b0}"),
      1, [](uint64_t a, uint64_t) -> uint64_t { return (~a & 0xFu) << 1; });
}

TEST(ConcatenationSynthesis, ALogicalNegationIsOneBitLong) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a", "{!a, a}"), 1,
      [](uint64_t a, uint64_t) -> uint64_t {
        return ((a == 0 ? 1u : 0u) << 4) | a;
      });
}

TEST(ConcatenationSynthesis, AComparisonIsOneBitLong) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a, input [3:0] b",
                        "{a == b, a}"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a == b ? 1u : 0u) << 4) | a;
      });
}

TEST(ConcatenationSynthesis, ALogicalAndIsOneBitLong) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a, input [3:0] b",
                        "{a && b, a}"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a != 0 && b != 0 ? 1u : 0u) << 4) | a;
      });
}

TEST(ConcatenationSynthesis, AConditionalIsAsLongAsItsLongerArm) {
  ExpectInputSweep(
      "module m(input [7:0] a, input s, output logic [8:0] y);\n"
      "  assign y = {s ? a : 4'b0000, 1'b0};\n"
      "endmodule\n",
      512, [](uint64_t v) -> uint64_t {
        uint64_t a = v & 0xFFu;
        return (v >> 8) != 0 ? a << 1 : 0;
      });
}

TEST(ConcatenationSynthesis, APowerOperandIsReportedForItsOperator) {
  ExpectAssignReported("input [3:0] a", "{a ** 2, 1'b0}",
                       "'a ** b', a to the power of b, has no lowering",
                       "11.4.3");
}

TEST(ConcatenationTarget,
     ProceduralAssignToAConcatenationIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [7:0] word, output logic [3:0] hi, output "
                   "logic [3:0] lo);\n"
                   "  always_comb {hi, lo} = word;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 2, ""));
}

}  // namespace
