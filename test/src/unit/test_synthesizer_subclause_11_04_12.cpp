#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_assign.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// Every case below fails on a netlist whose every output bit is constant zero,
// which is what the synthesizer answers for a concatenation without an arm for
// it. `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp switches on
// `expr->kind` and ends `default: return AigGraph::kConstFalse;`, so an
// `ExprKind::kConcatenation` that reaches that default drives every bit of the
// target to constant zero while the run reports success.

// The test fails on any lowering that builds nothing for a concatenation, since
// this is the first case. §11.4.12 defines a concatenation as the bits of one
// or more expressions joined together, and its example gives
// `{a, b[3:0], w, 3'b101}` as equivalent to
// `{a, b[3], b[2], b[1], b[0], w, 1'b1, 1'b0, 1'b1}`, so the leftmost operand
// takes the most significant bits. `a` is three bits wide and `b` is two rather
// than the two being equal, so a lowering that gives both the same offset, or
// that swaps which one is significant, disagrees at some value. Two operands of
// equal width would separate neither.
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

// The test fails on a lowering that reaches a signal operand and builds nothing
// for a literal one, which
// ConcatenationSynthesis.ConcatenationPlacesEachOperandAtItsOwnOffset passes.
// The literal is `2'b10` rather than `2'b00` or `2'b11` because those two read
// the same whichever order their bits are placed in.
TEST(ConcatenationSynthesis, ConcatenatedLiteralCarriesItsOwnBits) {
  ExpectInputSweep(
      "module m(input [2:0] a, output logic [4:0] y);\n"
      "  assign y = {a, 2'b10};\n"
      "endmodule\n",
      8, [](uint64_t a) { return (a << 2) | 2u; });
}

// The test fails on a lowering that answers nothing for a nested
// concatenation, which the two cases above pass. §11.4.12 makes a concatenation
// a packed vector of bits, so a concatenation is an operand of another
// concatenation.
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

// The test fails on a fix that answers constant zero for an operand whose width
// the synthesizer cannot compute and reports nothing, which is the silent wrong
// answer the three cases above are about, narrowed rather than removed.
// §11.4.12 needs each operand's size to work out the concatenation's whole
// size, so an operand whose width the synthesizer cannot compute is one it
// cannot place. `SynthLower::ExprWidth` reads no function's declaration, so a
// call is such an operand.
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

// The test fails on a fix that sizes an operator from whichever operand it can
// answer for. Table 11-21 makes `a + b` as long as the longer of its operands,
// so neither operand's length alone says how long it is, and an operand of
// unknown width on either side leaves the sum one the concatenation cannot
// place.
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

// The test fails on a lowering that places a shift inside a concatenation at
// the size and type of the assignment around it. §11.6.1 Table 11-21 marks the
// operands of a concatenation self-determined, and §11.8.1 rules the sign and
// size of such an operand its own, so `a >>> 1` is a signed four-bit shift and
// §11.4.10 fills its vacated top position with the sign bit of `a`. Under the
// unsigned eight-bit target it would be zero-filled instead, which disagrees at
// the eight values of `a` with bit 3 set.
TEST(ConcatenationSynthesis, AShiftOperandKeepsItsOwnSizeAndType) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [7:0] y", "input signed [3:0] a",
                        "{a >>> 1, 4'b0}"),
      1, [](uint64_t a, uint64_t) -> uint64_t {
        return ((a >> 1) | (a & 0x8u)) << 4;
      });
}

// The test fails on a lowering that sizes an operator expression from its
// literals alone and counts a name as no bits. §11.6.1 Table 11-21 makes `a |
// 4'b0000` as long as the longer of its operands, the eight bits of `a`, so
// every bit of `a` reaches `y` above the literal `1'b0`. Sized from the
// literal, the operand is four bits long and the netlist disagrees at every `a`
// from 16 up.
TEST(ConcatenationSynthesis, AnOperatorOperandIsAsLongAsItsLongerOperand) {
  ExpectInputSweep(
      "module m(input [7:0] a, output logic [8:0] y);\n"
      "  assign y = {a | 4'b0000, 1'b0};\n"
      "endmodule\n",
      256, [](uint64_t a) -> uint64_t { return a << 1; });
}

// The test fails on a lowering that finds no width in an operator expression
// over names alone, which refuses the concatenation below as having an operand
// it cannot place. Table 11-21 makes `a + b` three bits long, the longer of `a`
// and `b`, so the sum drops its carry and stands above the three bits of `a`.
// A lowering keeping the carry places `a` one bit too high.
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

// The test fails on a lowering that sizes a unary operator other than a
// reduction or `!` as anything but its operand. Table 11-21 makes `~a` as long
// as `a`, four bits, so all four complemented bits stand above the `1'b0`.
TEST(ConcatenationSynthesis, AComplementIsAsLongAsItsOperand) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a", "{~a, 1'b0}"),
      1, [](uint64_t a, uint64_t) -> uint64_t { return (~a & 0xFu) << 1; });
}

// The test fails on a lowering that sizes `!a` as its operand, which the case
// above passes. Table 11-21 makes `!` one bit long whatever its operand, so the
// result stands directly above the four bits of `a`.
TEST(ConcatenationSynthesis, ALogicalNegationIsOneBitLong) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a", "{!a, a}"), 1,
      [](uint64_t a, uint64_t) -> uint64_t {
        return ((a == 0 ? 1u : 0u) << 4) | a;
      });
}

// The test fails on a lowering that sizes a comparison as the longer of its
// operands. Table 11-21 makes the relational and equality operators one bit
// long, so `a == b` stands directly above the four bits of `a`.
TEST(ConcatenationSynthesis, AComparisonIsOneBitLong) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a, input [3:0] b",
                        "{a == b, a}"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a == b ? 1u : 0u) << 4) | a;
      });
}

// The test fails on a lowering that sizes a logical operator as the longer of
// its operands, which the case above passes. Table 11-21 makes `&&` one bit
// long as well, so `a && b` stands directly above the four bits of `a`.
TEST(ConcatenationSynthesis, ALogicalAndIsOneBitLong) {
  ExpectAssignSweep(
      ModuleAssigningTo("output logic [4:0] y", "input [3:0] a, input [3:0] b",
                        "{a && b, a}"),
      16, [](uint64_t a, uint64_t b) -> uint64_t {
        return ((a != 0 && b != 0 ? 1u : 0u) << 4) | a;
      });
}

// The test fails on a lowering that sizes `i ? j : k` from its literal arm
// alone. Table 11-21 makes the conditional operator as long as the longer of
// its two arms, the eight bits of `a`, so every bit of `a` reaches `y` above
// the `1'b0` where `s` is set.
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

// The test fails on a lowering that finds no width in `a ** 2` and refuses the
// concatenation for its operand, rather than for the operator it has no
// lowering for. Table 11-21 makes `**` as long as its left operand, so the
// concatenation has a width and the report names what is missing.
TEST(ConcatenationSynthesis, APowerOperandIsReportedForItsOperator) {
  ExpectAssignReported("input [3:0] a", "{a ** 2, 1'b0}",
                       "'a ** b', a to the power of b, has no lowering",
                       "11.4.3");
}

// The case below fails on a run that answers a netlist and reports nothing for
// an assignment whose target the synthesizer builds nothing for.
// `SynthLower::LowerContAssign` and `SynthLower::LowerAssignStmt` in
// src/synthesizer/synth_lower.cpp each return without touching the graph when
// the target is not an `ExprKind::kIdentifier`, and neither sets
// `lowering_incomplete_`, so `SynthLower::Lower` answers a graph that never
// drives the signal the source drives and the run reports success.
// `SynthLower::LowerStmt` in the same file already does the opposite for a
// statement it has no lowering for: it sets `lowering_incomplete_` and reports,
// and its comment says the location is what tells the reader which statement
// went missing.

// The test fails on a fix that assumes a concatenation target was already split
// into one assignment per element. §11.4.12 makes a concatenation a packed
// vector of bits that may stand on the left-hand side of an assignment. The
// cases above write their concatenation as the source of an assignment.
// `Elaborator::ElaborateContAssign` splits a concatenation target of a
// continuous assignment into one assignment per element, which is what
// VectorSelect.ConcatenationLvalueSplitLowersItsPartSelects in
// test/src/unit/test_synthesizer_subclause_11_05_01.cpp covers; nothing does
// the same for a procedural assignment.
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
