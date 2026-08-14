#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"
#include "helpers_synth_input_sweep.h"

using namespace delta;

namespace {

// Every case below fails on a netlist whose every output bit is constant zero,
// which is what the synthesizer answers for a replication without an arm for
// it. `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp switches on
// `expr->kind` and ends `default: return AigGraph::kConstFalse;`, so an
// `ExprKind::kReplicate` that reaches that default drives every bit of the
// target to constant zero while the run reports success.

// The test fails on any lowering that builds nothing for a replication, since
// this is the first case. §11.4.12.1 rules that a multiplier "indicates a
// joining together of that many copies of the concatenation", and gives
// `{4{w}}` the same value as `{w, w, w, w}`. The multiplier is 3 and `a` is two
// bits wide, so the copy index and the bit index within a copy are different
// numbers; a multiplier equal to the operand width would let a lowering that
// divided by the wrong one pass.
TEST(ReplicationSynthesis, ReplicationJoinsThatManyCopiesOfItsOperand) {
  ExpectInputSweep(
      "module m(input [1:0] a, output logic [5:0] y);\n"
      "  assign y = {3{a}};\n"
      "endmodule\n",
      4, [](uint64_t a) { return a | (a << 2) | (a << 4); });
}

// The test fails on a lowering that gives the replication the width of its
// operand rather than the multiplier times that width, which
// ReplicationSynthesis.ReplicationJoinsThatManyCopiesOfItsOperand does not
// reach because the replication is the whole right-hand side there. §11.4.12.1
// shows the nesting with `{b, {3{a, b}}}`.
TEST(ReplicationSynthesis, ReplicationInsideAConcatenationTakesItsOwnOffset) {
  ExpectInputSweep(
      "module m(input [1:0] a, input [2:0] b, output logic [6:0] y);\n"
      "  assign y = {b, {2{a}}};\n"
      "endmodule\n",
      32, [](uint64_t v) {
        uint64_t a = v & 0x3u;
        uint64_t b = (v >> 2) & 0x7u;
        return (b << 4) | (a << 2) | a;
      });
}

// The test fails on a fix that answers constant zero for a replicated operand
// whose width the synthesizer cannot compute and reports nothing, which is the
// silent wrong answer the two cases above are about, narrowed rather than
// removed. The rule is the one
// ConcatenationSynthesis.AnOperandOfUnknownWidthIsReported rests on, under
// §11.4.12.1 and for the operand being replicated: the size of each operand is
// needed to calculate the complete size, so an operand whose width the
// synthesizer cannot compute is one it cannot place.
TEST(ReplicationSynthesis, AnOperandOfUnknownWidthIsReported) {
  ExpectAssignReported("input [2:0] a, input [1:0] b", "{2{a + b}}",
                       "replication has no lowering", "11.4.12.1");
}

}  // namespace
