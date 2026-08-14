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
// this is the first case. §11.4.12 rules that "A concatenation is the result of
// the joining together of bits resulting from one or more expressions", and its
// example gives `{a, b[3:0], w, 3'b101}` as equivalent to `{a, b[3], b[2],
// b[1], b[0], w, 1'b1, 1'b0, 1'b1}`, so the leftmost operand takes the most
// significant bits. `a` is three bits wide and `b` is two rather than the two
// being equal, so a lowering that gives both the same offset, or that swaps
// which one is significant, disagrees at some value. Two operands of equal
// width would separate neither.
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
// concatenation, which the two cases above pass. §11.4.12 rules that "The
// concatenation is treated as a packed vector of bits", so a concatenation is
// an operand of another concatenation.
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
// §11.4.12 rules that "the size of each operand in the concatenation is needed
// to calculate the complete size of the concatenation", so an operand whose
// width the synthesizer cannot compute is one it cannot place.
TEST(ConcatenationSynthesis, AnOperandOfUnknownWidthIsReported) {
  ExpectAssignReported("input [2:0] a, input [1:0] b", "{a + b, a}",
                       "concatenation operand has no width", "11.4.12");
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
// into one assignment per element. §11.4.12 rules that a concatenation "is
// treated as a packed vector of bits" and "can be used on the left-hand side of
// an assignment". The cases above write their concatenation as the source of
// an assignment. `Elaborator::ElaborateContAssign` splits a concatenation
// target of a continuous assignment into one assignment per element, which is
// what VectorSelect.ConcatenationLvalueSplitLowersItsPartSelects in
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
