#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"
#include "helpers_synth_input_sweep.h"

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

}  // namespace
