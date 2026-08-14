#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// The test fails on a synthesizer that answers a netlist whose every bit of `y`
// is constant zero, which is what `assign y = a << 1;` lowers to today:
// `SynthLower::LowerBinaryBit` in src/synthesizer/synth_lower.cpp carries no
// arm for any of the four shift tokens, so a shift reaches `default: return
// AigGraph::kConstFalse;` on a module the synthesizer accepts without a word.
// §11.4.10 rules that the left shift moves each bit of the left operand up by
// the number of positions the right operand carries, so the netlist owes bit 0
// of `a` at bit 1 of `y` and so on up. The sweep drives `a` at 0 as well as at
// the other fifteen values, and 0 is the input that cannot fail here: a netlist
// of constant zeros agrees with a correct one there whatever it computes, so
// the fifteen non-zero values are what the case rests on.
TEST(ShiftSynthesis, LeftShiftByAConstantMovesEachBitUp) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 1"), 1,
                    [](uint64_t a, uint64_t) { return (a << 1) & 0xFu; });
}

// The test fails on a lowering that renumbers the bits in one direction only,
// which the case above passes. §11.4.10 gives `>>` the opposite direction to
// `<<`, so the netlist owes bit 1 of `a` at bit 0 of `y` and so on down, and
// the right shift arrives as its own token rather than as the left shift read
// backwards.
TEST(ShiftSynthesis, RightShiftByAConstantMovesEachBitDown) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a >> 1"), 1,
                    [](uint64_t a, uint64_t) { return a >> 1; });
}

// The test fails on a lowering that rotates rather than shifts. A rotate agrees
// with a shift by one at the two cases above for the bits it moves, and
// disagrees here because §11.4.10 rules that the vacated bit positions are
// filled with zeros rather than with the bits that left the top: `4'b1100 << 2`
// is 4'b0000 and not 4'b0011.
TEST(ShiftSynthesis, LeftShiftFillsTheVacatedPositionsWithZeros) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 2"), 1,
                    [](uint64_t a, uint64_t) { return (a << 2) & 0xFu; });
}

// The test fails on a lowering that zero-fills `>>>` whatever its operand was
// declared as. §11.4.10 rules that the arithmetic right shift "shall fill the
// vacated bit positions with ... the value of the most significant (i.e., sign)
// bit of the left operand if the result type is signed", so the eight values of
// `a` whose top bit is set are where this differs from `>>` and where a
// zero-filling lowering fails. The operand is declared signed and not only the
// target, because §11.8.1 rules that "Expression type depends only on the
// operands. It does not depend on the left-hand side (if any)".
TEST(ShiftSynthesis, ArithmeticRightShiftOfASignedOperandFillsWithTheSignBit) {
  ExpectAssignSweep(ModuleAssigningTo("output logic signed [3:0] y",
                                      "input signed [3:0] a", "a >>> 1"),
                    1,
                    [](uint64_t a, uint64_t) { return (a >> 1) | (a & 0x8u); });
}

// The test fails on a lowering that sign-fills every `>>>`, which the case
// above passes whole. §11.4.10 rules the fill is zeros "if the result type is
// unsigned", so what the vacated position carries turns on the type of the
// operand and not on the spelling of the operator, and the module below
// declares nothing signed.
TEST(ShiftSynthesis, ArithmeticRightShiftOfAnUnsignedOperandFillsWithZeros) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a >>> 1"), 1,
                    [](uint64_t a, uint64_t) { return a >> 1; });
}

// The test fails on a lowering that reads a constant right operand and builds
// nothing for one that arrives on a port, which the five cases above pass whole
// because each shifts by a literal. §11.4.10 asks for the shift by the value
// the right operand carries, so the netlist owes a shifter selecting between
// the four distances `s` can name rather than one fixed renumbering. Every one
// of the sixty-four combinations of the two operands is driven.
TEST(ShiftSynthesis, ShiftByAVariableAmountShiftsByTheValueItCarries) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a, input [1:0] s", "a << s"),
                    4, [](uint64_t a, uint64_t b) { return (a << b) & 0xFu; });
}

}  // namespace
